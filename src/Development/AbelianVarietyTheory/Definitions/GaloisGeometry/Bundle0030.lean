import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.AddCharThetaLawRearrangementIdentity
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0009
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ActEEqOfConjRelated
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.MainNotions.N IsDedekindDomain NumberField
open Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NJoin.Model

variable {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} {X : RealAt D cf nch tp}
  {M : MtFam D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}

def actE {Γ W : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ Γ W) (g : Γ) : W ≃ₗ[ℂ] W :=
  LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)

theorem actE_eq_of_conj_related {Γ W : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ Γ W) (g h : Γ) {x y : W}
    (e : x = ρ (g⁻¹ * h * g) y) : actE ρ g x = ρ h (actE ρ g y) := by
  show ρ g x = ρ h (ρ g y)
  rw [e, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

theorem block_frame_conjugation_identity {H : Type} [Group H] (S : Subgroup H) (g h : S) (a : H) :
    ((g : H) * a)⁻¹ * h * (g * a) = a⁻¹ * ((g⁻¹ * h * g : S) : H) * a := by
  push_cast
  group

theorem inv_aux {H : Type} [Group H] (g a h : H) : a⁻¹ * (g⁻¹ * h) = (g * a)⁻¹ * h := by group

theorem real_apply_eq_actE_real_inv_mul {μ j} (m : MtReal D μ j) (x) (g : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (h : Formalism.AUTREP.GAf D.host.E D.R.nV) :
    m.real x h = actE m.wt.ρ g (m.real x ((g : Formalism.AUTREP.GAf D.host.E D.R.nV)⁻¹ * h)) := by
  have hm : m.real x ∈ NG.TypeSp m.wt.ρ m.J m.χ := m.real_range ▸ LinearMap.mem_range_self _ x
  exact (congrArg (m.real x) (mul_inv_cancel_left _ h).symm).trans (hm.1.1 g _)

def shift (A : Agree X M rep) (g : Fin D.R.m → ReciprocityTheory.Aut.GQ D.host.E D.R.nV) : Agree X M rep where
  hF := A.hF
  PV := A.PV
  stdV := A.stdV
  stdW := A.stdW
  a j := (g j : Formalism.AUTREP.GAf D.host.E D.R.nV) * A.a j
  rat j h := by
    have e : ((g j : Formalism.AUTREP.GAf D.host.E D.R.nV) * A.a j)⁻¹ * h * ((g j : Formalism.AUTREP.GAf D.host.E D.R.nV) * A.a j) =
        (A.a j)⁻¹ * ((g j : Formalism.AUTREP.GAf D.host.E D.R.nV)⁻¹ * h * g j) * A.a j := by group
    rw [e, ← A.rat j]
    constructor
    · intro hh
      exact mul_mem (mul_mem (inv_mem (g j).2) hh) (g j).2
    · intro hh
      have := mul_mem (mul_mem (g j).2 hh) (inv_mem (g j).2)
      simpa [mul_assoc] using this
  eW μ hμ j := (A.eW μ hμ j).trans
    (actE (M μ (j.1 + 1) (by omega) (by omega)).wt.ρ (g j))
  wt μ hμ j h γ hγ eq v :=
    actE_eq_of_conj_related _ (g j) h (A.wt μ hμ j ((g j)⁻¹ * h * g j) γ hγ
      (eq.trans (congrArg (fun z => finHom (Vc D j) ((A.PV j).ψ z)) (block_frame_conjugation_identity _ (g j) h (A.a j)))) v)
  real μ hμ j x h :=
    (real_apply_eq_actE_real_inv_mul (M μ (j.1 + 1) (by omega) (by omega)) x (g j) h).trans
      (congrArg (actE (M μ (j.1 + 1) (by omega) (by omega)).wt.ρ (g j)) ((A.real μ hμ j x _).trans
        (congrArg (fun z => A.eW μ hμ j (X.fn hμ j x ((A.PV j).ψ z))) (inv_aux _ _ _))))
  rep_iso := A.rep_iso

theorem shift_a (A : Agree X M rep) (g : Fin D.R.m → ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (j) :
    (shift A g).a j = g j * A.a j := rfl

theorem real_eq {M' : MtFam D} (A : Agree X M rep) (A' : Agree X M' rep) (hP : A.PV = A'.PV) (ha : A.a = A'.a)
    {μ} (hμ : Used0 D μ) (j : Fin D.R.m) (x) (h) :
    (A'.eW μ hμ j).symm ((M' μ (j.1 + 1) (by omega) (by omega)).real x h) =
      (A.eW μ hμ j).symm ((M μ (j.1 + 1) (by omega) (by omega)).real x h) := by
  rw [A.real μ hμ, A'.real μ hμ, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hP, ha]

theorem eq_zero_of_fin (A : Agree X M rep) {μ} (hμ : Used0 D μ) (j : Fin D.R.m) (x : D.what₂.Mt μ (j.1 + 1))
    (hx : ∀ g ∈ GfC (Vc D j), X.fn hμ j x g = 0) : x = 0 := by
  apply (M μ (j.1 + 1) (by omega) (by omega)).real_inj
  funext h
  rw [A.real μ hμ, hx _ ((A.PV j).into _), map_zero, map_zero]
  rfl

theorem rep_inj (A : Agree X M rep) (σ σ' : D.what₂.FT) (h : rep σ = rep σ') : σ = σ' := by
  obtain ⟨T, hT⟩ := A.iso_rep σ
  obtain ⟨T', hT'⟩ := A.iso_rep σ'
  apply X.eFT.injective
  apply rowRepR_inj X.R.θ
  revert T hT
  rw [h]
  intro T hT
  refine ⟨T.symm.trans T', fun k f f' e => ?_⟩
  apply hT'
  have hm := (rep σ').stable k _ (T.symm f).2
  have h2 := hT k (T.symm f) ⟨_, hm⟩ rfl
  have h4 : T (T.symm f) = f := T.apply_symm_apply f
  have h3 : T ⟨_, hm⟩ = f' := Subtype.ext (h2.trans ((congrArg (fun z : (X.rep σ).S => NG.rt D.host.E D.R.r k z.1) h4).trans e.symm))
  exact congrArg Subtype.val (T.symm_apply_eq.2 h3.symm)

theorem canon_phi_inj (j : Fin D.R.m) (Y : GlobalTheory.NPin.RowMod D rep (j.1 + 1)) (h : IsCanon X j rfl Y) :
    Function.Injective Y.φ := by
  obtain ⟨e, c, -, -, -, -, -, h6⟩ := h
  intro y y' hy
  apply (X.IL.jMj j).injective
  apply Subtype.ext
  rw [← h6, ← h6]
  exact congrArg (fun z => PiTensorProduct.lift (e z)) hy

end GlobalTheory.NJoin.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ResidualIrreducibilityFormsEquivalent
section
noncomputable section

namespace GlobalTheory.NFacts

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

structure Core (D : D7) : Prop where
  what₂ : GlobalTheory.NRows.Rows D
  adm : SumRepresentations.admitted D
  Conclusion1 : SumRepresentations.Conclusion1 D
  Conclusion2 : SumRepresentations.Conclusion2 D
  rhoBar : ResidualIrreducibleRankR D
  g3p : AdmissibleThreePrime.LabelDegreeHypotheses D
  weight : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D
  block : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D
  g2 : AdmissibleParameterJ.DeRhamFamilyAway D ∧ AdmissibleParameterJ.DeRhamFamilyTypePrimes D
  admJ : ∀ L : SizeData₂ D, AdmissibleParameterJ.AdmPar L → AdmissibleParameterJ.AdmJ L
  muUnr : GlobalTheory.HubX.MuUnr D
  depthG : GlobalTheory.HubX.DepthZeroG D
  bc : SphericalInertData.Conclusion1 D
  lam : GlobalTheory.NRows.LamUsed D

structure Facts (D : D7) (C : NChoice D) : Prop extends Core D where
  c2 : KillingConditions.LocalisationUniqueness D
  large : GlobalTheory.CoefDuty.Large D
  duties : GlobalTheory.CoefDuty.Duties D
  nct : NChTie D C
  trip : GlobalTheory.PtCore.TriplesGood D
  same : GlobalTheory.PtCore.SameTwist D C
  good : GoodFTAll D

theorem Core.admA {D : D7} (h : Core D) : SumRepresentations.AdmA D := h.adm.1.1

theorem Core.a3 {D : D7} (h : Core D) (L : SizeData₂ D) : TwistedPlaces.adm3 L := h.what₂.rank L

theorem Core.isot {D : D7} (h : Core D) : Rows.IsotInternal D.what₂ := h.adm.2.2

theorem residualIrreducibility_forms_equivalent (D : D7) : SumRepresentations.adm6 D ↔ ResidualIrreducibleRankR D := Iff.rfl

end GlobalTheory.NFacts

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnitaryRealisationReadingOfIdempotentActsViaLeve
section
noncomputable section

namespace GlobalTheory.NRows.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy

theorem used_loc (D : D7) (i : D.nd.Loc) : D.nd.mu i = D.what₂.mu0 ∨ ∃ w, D.nd.mu i = D.what₂.muAt w :=
  Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩

theorem lamPos_of_used {D : D7} (h : LamUsed D) {μ} (hμ : μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : LamPos D μ j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact h μ hμ ⟨k, by omega⟩

theorem lamLoc {D : D7} (h : LamUsed D) (i : D.nd.Loc) : LamPos D (D.nd.mu i) (D.nd.j i) :=
  lamPos_of_used h (used_loc D i) (D.nd.j_range i).1 (D.nd.j_range i).2

theorem up_injective {D : D7} {μ} {j : ℕ} (h : LamPos D μ j) (hI : DirectSum.IsInternal (D.what₂.isot j)) :
    Function.Injective (D.what₂.thetaT μ j) := by
  have hs : Function.Surjective (D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hI.submodule_iSup_eq_top, iSup_le_iff]
    intro σ f hf
    by_cases h0 : D.what₂.isot j σ = ⊥
    · rw [h0] at hf
      rw [(Submodule.mem_bot ℂ).1 hf]
      exact zero_mem _
    · have hl : ((D.what₂.lamP μ j σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ((h σ).2 h0).ne'
      refine ⟨((D.what₂.lamP μ j σ : ℝ) : ℂ)⁻¹ • f, ?_⟩
      rw [map_smul, LinearMap.comp_apply, (h σ).1 f hf, smul_smul, inv_mul_cancel₀ hl, one_smul]
  have hi := LinearMap.injective_iff_surjective.2 hs
  rw [LinearMap.coe_comp] at hi
  exact hi.of_comp

theorem rank_of {D : D7} (hI : SumRepresentations.adm8 D) (h : LamUsed D) (L : SizeData₂ D) : TwistedPlaces.adm3 L := by
  intro j hj w hw
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  have e : D.what₂.muTw w = D.what₂.muAt w := ((D.what₂.muAt_or w).resolve_left hw).symm
  have a := up_injective (lamPos_of_used h (Or.inr ⟨w, e⟩) h1 h2) (hI j h1 h2)
  have b := up_injective (lamPos_of_used h (Or.inl rfl) h1 h2) (hI j h1 h2)
  unfold SizeData₂.zeroSpaceRankAtPlace SizeData₂.dZ0 Rows.Data.Zj
  rw [LinearMap.finrank_range_of_inj a, LinearMap.finrank_range_of_inj b]

theorem not_lamUsed {D : D7} (j : Fin D.R.m) (σ : D.what₂.FT) (hσ : D.what₂.isot (j.1 + 1) σ ≠ ⊥)
    (h0 : D.what₂.thetaP D.what₂.mu0 (j.1 + 1) = 0) : ¬ LamUsed D := by
  intro h
  obtain ⟨f, hf, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
  have h1 := (h _ (Or.inl rfl) j σ).1 f hf
  have hl : ((D.what₂.lamP D.what₂.mu0 (j.1 + 1) σ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ((h _ (Or.inl rfl) j σ).2 hσ).ne'
  rw [h0, LinearMap.zero_apply] at h1
  exact hne ((smul_eq_zero.1 h1.symm).resolve_left hl)

theorem mtPar_holds (D : D7) : MtParTie D.nd D.naut D.ntypes := D.mtpar_tie

theorem goodIdempotent_iff_rowProjector (D : D7) : GoodIdempotentFixesLocalisationForms D ↔ ∀ (i : D.nd.Loc) (σ' : D.ntypes.Par),
    ∀ F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ', D.ntypes.goodPar σ' → D.what₂.eMt (D.nd.mu i) (D.nd.j i) F = F := by
  simp only [GoodIdempotentFixesLocalisationForms, D.nStage_trivialCharacter_compat.2]

theorem goodIdempotent_of_goodProjector {D : D7} (h : ArithmeticCylinders.Conclusion4 D) : GoodIdempotentFixesLocalisationForms D :=
  fun i σ' F hF hg => (h.2.2.2.2.1 _ _ (D.nd.j_range i).1 (D.nd.j_range i).2 σ' F hF).1 hg

theorem partsGive_of_stmt {D : D7} (h : SumRepresentations.IntegralityFromMetric D) : PartsGive D := fun a _ _ _ _ _ _ => h a

theorem baseChange_preserves_unitary_of {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (h : PartsGive D) (I : Inputs hL D) (a : RowsA D) (b : RowsB D) :
    SumRepresentations.Conclusion1 D :=
  h ⟨⟨a.tie0, I.hypO, base_change_automorphic_of D I.bc I.c1, a.a2, b.a3, b.a4, a.a5⟩, a.temp⟩ a.tieLab b.rowSize a.hecke
    (lamLoc I.lam) b.thetaOne a.g4p

theorem an_of {D : D7} (h : SumRepresentations.adm5 D) : IsobaricCuspidalStrongMultiplicityOne D.nd D.naut ∧ IsobaricDiscreteSelfDualStrongMultiplicityOne D.nd D.naut := ⟨h.1, h.2.1⟩

section Read
variable {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch}
  (X : GlobalTheory.NJoin.RealAt D cf nch tp)

theorem exists_vec {μ} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (f : D.what₂.Mt μ (j.1 + 1)) :
    ∃ y, X.R.extV j (X.tupT μ) y = X.fn hμ j f := (X.IL.jMt μ hμ j f).2.1

theorem goodVt_zero (j : Fin D.R.m) (t : X.T) : GlobalTheory.DownLift.GoodVt X.R j t 0 := by
  intro l
  have : (fun h => l (X.R.extV j t 0 h)) = 0 := by
    funext h
    simp
  rw [this, map_zero]

theorem good_of_fixed (h : GoodIdempotentReadsAsGoodTypeProjector X) {μ} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (f : D.what₂.Mt μ (j.1 + 1))
    (y) (hy : X.R.extV j (X.tupT μ) y = X.fn hμ j f) (hf : D.what₂.eMt μ (j.1 + 1) f = f) :
    GlobalTheory.DownLift.GoodVt X.R j (X.tupT μ) y := by
  have h2 : D.ntypes.onMt μ (j.1 + 1) D.ntypes.e0 f = f := by rw [← D.nStage_trivialCharacter_compat.2]; exact hf
  have h3 := h μ hμ j f y hy
  exact h3.1 h2

end Read

def PartNe (D : D7) : Prop := 0 < D.R.m ∧ ∃ σ : D.what₂.FT, ∀ j : Fin D.R.m, ∃ f ∈ D.what₂.isot (j.1 + 1) σ, f ≠ 0

theorem lamUsed_of_id (D : D7) (h : ∀ μ j f, D.what₂.thetaP μ j (D.what₂.thetaT μ j f) = f)
    (h1 : ∀ μ j σ, D.what₂.lamP μ j σ = 1) : LamUsed D := fun μ _ j σ =>
  ⟨fun f _ => by rw [h, h1, Complex.ofReal_one, one_smul], fun _ => by rw [h1]; exact one_pos⟩

theorem lamUsed_model : ∃ D : D7, LamUsed D ∧ PartNe D :=
  ⟨GlobalTheory.Core.Int.Inhab.recOne, lamUsed_of_id _
    (fun _ _ f => congrArg (fun g => g f) (LinearMap.adjoint_id (𝕜 := ℂ) (E := Formalism.BasicNotions.Examples₂.NZ.En 1))) (fun _ _ _ => rfl),
    by decide, (), fun _ => ⟨Formalism.BasicNotions.Examples₂.NZ.eb 1 0,
      (show Formalism.BasicNotions.Examples₂.NZ.eb 1 0 ∈ Submodule.span ℂ (Formalism.BasicNotions.Examples₂.NZ.eb 1 '' {_σ | () = ()}) from
        Submodule.subset_span ⟨0, rfl, rfl⟩),
      (Formalism.BasicNotions.Examples₂.NZ.eb 1).toBasis.ne_zero 0⟩⟩

theorem rowsC_of_isEmpty (D : D7) [h : IsEmpty D.nd.Loc] : RowsC D :=
  ⟨fun _ _ _ _ _ i => h.elim i, fun i => h.elim i, fun i => h.elim i, fun i => h.elim i, fun i => h.elim i,
    fun i => h.elim i⟩

theorem serLoc_of_isEmpty (D : D7) [h : IsEmpty D.nd.Loc] : GlobalTheory.TypeLeaf.SerLoc D := fun i => h.elim i

theorem definite_of_tied {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (T : Tied hL D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    (letI := D.host.cmStar; (D.sp.V j).IsDefinite) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have h := T.X.given.core.models.vpos ⟨k, by omega⟩
  intro τ
  exact Or.inl (h τ)

theorem loc_of_tied {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (T : Tied hL D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (w : D.what₂.places.Pl) (hw : D.what₂.muAt w ≠ D.what₂.mu0) [Nontrivial (T.P.H.cover.B.V j w)] :
    ∃ i : D.nd.Loc, D.nd.j i = j ∧ D.nd.w i = w := by
  haveI : Nontrivial (Formalism.L2.heckeAlg T.P.H.cover.B j w) := inferInstance
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (Formalism.L2.heckeAlg T.P.H.cover.B j w)
  obtain ⟨i, hi, -⟩ := T.P.H.cover.mx_all j w h1 h2 hw I hI
  exact ⟨i, (D.nd.locs_mem _ _ _).1 hi⟩

theorem eq_zero_of_good {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp) (h : GoodIdempotentReadsAsGoodTypeProjector X) {μ} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m)
    (h0 : D.what₂.eMt μ (j.1 + 1) = 0) (f : D.what₂.Mt μ (j.1 + 1)) (y) (hy : X.R.extV j (X.tupT μ) y = X.fn hμ j f)
    (hg : GlobalTheory.DownLift.GoodVt X.R j (X.tupT μ) y) : f = 0 := by
  have h2 := (h μ hμ j f y hy).2 hg
  rw [← D.nStage_trivialCharacter_compat.2, h0] at h2
  exact h2.symm

theorem loc_of_inputs {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (I : Inputs hL D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (σ : D.what₂.FT) (hσ : D.what₂.isot j σ ≠ ⊥) (w : D.what₂.places.Pl) (hw : D.what₂.muAt w ≠ D.what₂.mu0) :
    ∃ i : D.nd.Loc, D.nd.j i = j ∧ D.nd.w i = w := by
  have e : D.what₂.muTw w = D.what₂.muAt w := ((D.what₂.muAt_or w).resolve_left hw).symm
  have a := up_injective (lamPos_of_used I.lam (Or.inr ⟨w, e⟩) h1 h2) (I.isot j h1 h2)
  obtain ⟨f, -, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
  have hne : D.what₂.thetaT (D.what₂.muTw w) j f ≠ 0 := fun h => hf (a (h.trans (map_zero _).symm))
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  have hidx : Nonempty (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have h3 := (D.what₂.jMt_basis (D.what₂.muTw w) j b).2
    rw [Set.range_eq_empty, Submodule.span_empty] at h3
    exact hne ((Submodule.mem_bot ℂ).1 (h3 ▸ Submodule.mem_top))
  obtain ⟨k⟩ := hidx
  haveI : Nontrivial (I.P.H.cover.B.V j w) := ⟨⟨_, 0, (I.P.H.cover.B.iV_basis j w b).1.ne_zero k⟩⟩
  exact loc_of_tied I.toRowSideFamily j h1 h2 w hw

theorem rows_model : ∃ D : D7, LamUsed D ∧ PartNe D ∧ SumRepresentations.adm8 D ∧ ∀ L : SizeData₂ D, TwistedPlaces.adm3 L := by
  have h : LamUsed GlobalTheory.Core.Int.Inhab.recOne := lamUsed_of_id _
    (fun _ _ f => congrArg (fun g => g f) (LinearMap.adjoint_id (𝕜 := ℂ) (E := Formalism.BasicNotions.Examples₂.NZ.En 1))) (fun _ _ _ => rfl)
  have hp : PartNe GlobalTheory.Core.Int.Inhab.recOne := ⟨by decide, (), fun _ => ⟨Formalism.BasicNotions.Examples₂.NZ.eb 1 0,
      (show Formalism.BasicNotions.Examples₂.NZ.eb 1 0 ∈ Submodule.span ℂ (Formalism.BasicNotions.Examples₂.NZ.eb 1 '' {_σ | () = ()}) from
        Submodule.subset_span ⟨0, rfl, rfl⟩),
      (Formalism.BasicNotions.Examples₂.NZ.eb 1).toBasis.ne_zero 0⟩⟩
  have h8 : SumRepresentations.adm8 GlobalTheory.Core.Int.Inhab.recOne := by
    intro j _ _
    haveI : Unique GlobalTheory.Core.Int.Inhab.recOne.what₂.FT := inferInstanceAs (Unique Unit)
    have ht : ∀ σ, GlobalTheory.Core.Int.Inhab.recOne.what₂.isot j σ = ⊤ := fun _ => by
      show Submodule.span ℂ (Formalism.BasicNotions.Examples₂.NZ.eb 1 '' {_σ | () = ()}) = ⊤
      have : ({_σ | () = ()} : Set (Fin 1)) = Set.univ := by ext; simp
      rw [this, Set.image_univ]
      exact (Formalism.BasicNotions.Examples₂.NZ.eb 1).toBasis.span_eq
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨iSupIndep_subsingleton _, ?_⟩
    rw [eq_top_iff, ← ht default]
    exact le_iSup _ default
  exact ⟨_, h, hp, h8, rank_of h8 h⟩

theorem baseChangeConditions_of_tied {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (T : Tied hL D) : GlobalDatumCompatibility D :=
  GlobalTheory.DesignBC.jointCond_of_definite D (definite_of_tied T)

theorem bc_iff_of_tied {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (T : Tied hL D) :
    SphericalInertData.Conclusion1 D ↔ ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ π : D.nbc.AU j, SphericalInertData.SphInert D.nd D.naut D.nbc j π →
      ∃ Pa, SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa :=
  ⟨fun h j h1 h2 => h (baseChangeConditions_of_tied T).1 (hypCM_of D (baseChangeConditions_of_tied T)) j h1 h2 (nV_pos D) (definite_of_tied T j h1 h2),
    fun h _ _ j h1 h2 _ _ => h j h1 h2⟩

theorem eC_eq {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp) : ∃ eR : X.G ≃* G0g D.nd, ∀ g,
      Formalism.IndefR.Links.RealDat.eC (A := X.A) D.what₂.embLL g = D.ntypes.e0.coeff (eR g) := by
  obtain ⟨eR, -, -, h, -⟩ := X.given.core.grp.record
  exact ⟨eR, h⟩

theorem unitaryRealisationReading_of_idempotent_acts_via_levelGroup {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (h : ∀ μ (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (f : D.what₂.Mt μ (j.1 + 1))
      (l : (X.R.cV j).W →ₗ[ℂ] ℂ),
      Formalism.IndefR.Links.gaL (Formalism.IndefR.Links.Vc D j) (X.R.βV j) (X.R.datVt j (X.tupT μ)) X.R.eG
        (Formalism.IndefR.Links.RealDat.eC (A := X.A) (Formalism.IndefR.Links.sg0 D X.A)) (fun g => l (X.fn hμ j f g)) =
        fun g => l (X.fn hμ j (D.ntypes.onMt μ (j.1 + 1) D.ntypes.e0 f) g)) : GoodIdempotentReadsAsGoodTypeProjector X := by
  intro μ hμ j f y hy
  unfold GlobalTheory.DownLift.GoodVt
  rw [hy]
  constructor
  · intro hf l
    rw [h μ hμ j f l, hf]
  · intro hg
    apply (X.IL.jMt μ hμ j).injective
    apply Subtype.ext
    funext g
    have key : ∀ l : (X.R.cV j).W →ₗ[ℂ] ℂ,
        l (X.fn hμ j (D.ntypes.onMt μ (j.1 + 1) D.ntypes.e0 f) g - X.fn hμ j f g) = 0 := fun l => by
      rw [map_sub, sub_eq_zero]
      exact congrFun ((h μ hμ j f l).symm.trans (hg l)) g
    exact sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ (V := (X.R.cV j).W) _).1 key)

theorem not_rows_of_dup (D : D7) (ν ν' : D.naut.CG 1) (hne : ν ≠ ν') (h : ∀ w, D.naut.locG ν w = D.naut.locG ν' w) :
    ¬ Rows D := fun r => hne (r.a.hecke ν ν' (Filter.Eventually.of_forall fun w _ => h w))

theorem lift_ne {D : D7} (h : LamUsed D) (i : D.nd.Loc) (σ : D.what₂.FT) (hσ : D.what₂.isot (D.nd.j i) σ ≠ ⊥) :
    (D.what₂.isot (D.nd.j i) σ).map (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) ≠ ⊥ := by
  intro h0
  obtain ⟨f, hf, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
  have h1 := (h.loc i σ).1 f hf
  have h2 : D.what₂.thetaT (D.nd.mu i) (D.nd.j i) f = 0 :=
    (Submodule.mem_bot ℂ).1 (h0 ▸ Submodule.mem_map_of_mem hf)
  have hl : ((D.what₂.lamP (D.nd.mu i) (D.nd.j i) σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ((h.loc i σ).2 hσ).ne'
  rw [h2, map_zero] at h1
  exact hne ((smul_eq_zero.1 h1.symm).resolve_left hl)

end GlobalTheory.NRows.Model

end
end

