import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0907
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0904
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0104
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularFrameChangeOfTriangularPeriod
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0081
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DatEqOfPhiHat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0910

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass
  GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct

namespace GlobalTheory.UseLoc.Cases

section Gen

variable {O : Type} (LL : Type) [CommRing O] [Field LL] [Algebra O LL]

def intO : Submodule O LL := LinearMap.range (Algebra.linearMap O LL)

def Xq (lam : O) (a : ℕ) : Submodule O (LL ⧸ intO (O := O) LL) :=
  LinearMap.ker (lam ^ a • (LinearMap.id : (LL ⧸ intO (O := O) LL) →ₗ[O] (LL ⧸ intO (O := O) LL)))

variable {LL}
variable {V V' : Type} [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module LL V'] [Module O V']
  [IsScalarTower O LL V']

def scalQ (T : Submodule O V) (T' : Submodule O V') (j : V →ₗ[O] V') (hj : ∀ v ∈ T, j v ∈ T') (t : ↥T) :
    (LL ⧸ intO (O := O) LL) →ₗ[O] V' ⧸ T' :=
  (intO (O := O) LL).liftQ (T'.mkQ ∘ₗ (LinearMap.id : LL →ₗ[O] LL).smulRight (j t)) (by
    rintro _ ⟨c, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.smulRight_apply, LinearMap.id_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Algebra.linearMap_apply, algebraMap_smul]
    exact T'.smul_mem c (hj t t.2))

def scalB (T : Submodule O V) (T' : Submodule O V') (j : V →ₗ[O] V') (hj : ∀ v ∈ T, j v ∈ T') :
    ↥T →ₗ[O] (LL ⧸ intO (O := O) LL) →ₗ[O] V' ⧸ T' where
  toFun := scalQ T T' j hj
  map_add' t u := by
    apply Submodule.linearMap_qext
    ext s
    simp [scalQ, smul_add]
  map_smul' c t := by
    apply Submodule.linearMap_qext
    ext s
    simp [scalQ, smul_comm s c]

def iotaG (T : Submodule O V) (T' : Submodule O V') (j : V →ₗ[O] V') (hj : ∀ v ∈ T, j v ∈ T') :
    ↥T ⊗[O] (LL ⧸ intO (O := O) LL) →ₗ[O] V' ⧸ T' :=
  TensorProduct.lift (scalB T T' j hj)

theorem iotaG_tmul (T : Submodule O V) (T' : Submodule O V') (j : V →ₗ[O] V') (hj : ∀ v ∈ T, j v ∈ T')
    (t : ↥T) (s : LL) :
    iotaG T T' j hj (t ⊗ₜ Submodule.Quotient.mk s) = Submodule.Quotient.mk (s • j t) := rfl

end Gen

section Conc

variable {O : Type} (LL : Type) [CommRing O] [Field LL] [Algebra O LL]

def iotaW (lam : O) (a k : ℕ) :
    ↥(stdG O LL k) ⊗[O] ↥(Xq LL lam a) →ₗ[O] (Fin k → LL) ⧸ stdG O LL k :=
  iotaG (stdG O LL k) (stdG O LL k) LinearMap.id (fun _ h => h) ∘ₗ LinearMap.lTensor _ (Xq LL lam a).subtype

def constOne : LL →ₗ[O] (Fin 1 → LL) := LinearMap.pi fun _ => LinearMap.id

theorem constOne_mem : ∀ v ∈ intO (O := O) LL, constOne (O := O) LL v ∈ stdG O LL 1 := by
  rintro _ ⟨c, rfl⟩
  simp only [constOne, stdG]
  refine ⟨fun _ => c, ?_⟩
  ext i
  simp

def iotaC (lam : O) (a : ℕ) :
    ↥(intO (O := O) LL) ⊗[O] ↥(Xq LL lam a) →ₗ[O] (Fin 1 → LL) ⧸ stdG O LL 1 :=
  iotaG (intO LL) (stdG O LL 1) (constOne LL) (constOne_mem LL) ∘ₗ LinearMap.lTensor _ (Xq LL lam a).subtype

variable {LL}

def latOne (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] (ψ : G →* Oˣ) :
    Lattice (O := O) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := LL) ψ)) where
  T := intO LL
  stable g x hx := by
    obtain ⟨c, rfl⟩ := hx
    refine ⟨((ψ g : Oˣ) : O) * c, ?_⟩
    simp [Formalism.WeaklyAdmissibleFiltrations.charRep, tableLineDegreeTwo.charL, Algebra.linearMap_apply, Algebra.smul_def]
  fg := by
    rw [intO, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O LL) hinj)
  span := by
    rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ Submodule.span LL ((intO (O := O) LL : Set LL)) :=
      Submodule.subset_span ⟨1, map_one (algebraMap O LL)⟩
    simpa using Submodule.smul_mem _ x h1

end Conc

end GlobalTheory.UseLoc.Cases

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysWpRTw
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLoc

theorem locC_rTwO {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x) = twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹ := by
  let ψ : D.nd.O i →+* ↥C.LL.1 := C.inc.comp (D.nbr i w hw).toLL
  let j : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  refine MonoidHom.ext fun g => ?_
  refine Matrix.ext fun a b => ?_
  exact map_mul ψ (((chiU D.nd i 1)⁻¹ (j g) : (D.nd.O i)ˣ) : D.nd.O i) (rO D.nd i r x (j g) a b)

theorem crys_Wp_rTw : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) ∧ ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
  intro D i r ρ π w hw C _ _ hG hd
  have h2 : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
    intro x
    rw [locC_rTwO]
    exact (hG w hw C).2 x
  refine ⟨?_, h2⟩
  obtain ⟨e, he⟩ := hd
  have hd' : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := by
    refine ⟨e, fun g u => ?_⟩
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.overK, GlobalTheory.SummandJumps.matRep_apply]
    exact he g u
  exact ((GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρ π hd').1 (h2 π)).1

end GlobalTheory.UseLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeWachModuleExistsProofStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLatticeWachModuleExists_proof : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), WAll D HW F := by
  first | exact @GlobalTheory.NLink.wAll_holds | exact GlobalTheory.NLink.wAll_holds | (intros; apply GlobalTheory.NLink.wAll_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroOfPrintsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depth_zero_of_localLanglands : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → GlobalTheory.HubX.DepthZeroG D := by
  first | exact @GlobalTheory.DepthZeroType.main | exact GlobalTheory.DepthZeroType.main | (intros; apply GlobalTheory.DepthZeroType.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoverDictionaryAdelicElementComponent
section
noncomputable section

namespace GlobalTheory.CoverOnto

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Matrix
open GlobalTheory.ShortMove GlobalTheory.ShortMoveIso GlobalTheory.TwistTie

set_option maxHeartbeats 1000000 in

theorem frBor_of_isometry {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (hr : 1 ≤ Dw.p + Dw.q) (hσ : GoodEmb c σ) (hA : l.A = 1) {k k' : Fin F.n}
    (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k').La)
    (hEF : ∀ a b, (F.Di k').EF (gam a) (gam b) = (F.Di k).EF a b)
    (hM : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ x, gam (F.t k a) = F.t k' a + l.M • x)
    {P : (F.Di k).La →+ (Fin g → ℂ)} {P' : (F.Di k').La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P) (hP' : IsPeriod (F.Di k') (fun j => relab c σ (e j).1) P')
    (h : ∀ a, P' (gam a) = P a) (y y' : FrPt Xo c (CAt σ)) (hy : y.x = F.u k P) (hy' : y'.x = F.u k' P')
    (hu : ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i))
    (hu' : ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k' P' z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y'.u τ i)) :
    ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t y y' := by
  classical
  have hty := (GlobalTheory.Relab.relab_good _ H l c σ hσ).2.2.2 Dw g e
  have hpt := point_eq_of_isometry F hr hσ hty hA gam hEF hM hP hP' h
  obtain rfl := F.disj k k' P P' hP hP' hpt
  obtain ⟨m, hm⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hM' : ∀ b ∈ Mfr l • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ x, gam b = b + l.M • x := by
    intro b hb
    refine Submodule.smul_induction_on hb (fun s hs b _ => ?_) ?_
    · obtain ⟨a, d, rfl⟩ := F.t_surj k b
      obtain ⟨x, hx⟩ := hM (s • a) (Submodule.smul_mem_smul hs Submodule.mem_top)
      refine ⟨x + m • (gam (s • d) - s • d), ?_⟩
      rw [smul_add, ← map_smul, map_add, hx, smul_comm s l.M' d, map_nsmul, hm, smul_add, ← mul_smul, smul_sub]
      abel
    · rintro a b ⟨x, hx⟩ ⟨z, hz⟩
      exact ⟨x + z, by rw [map_add, hx, hz, smul_add]; abel⟩
  obtain ⟨-, -, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F k P P' gam 1 hP hP' hEF hM'
    (fun a => ⟨gam a - a, by rw [hA, one_smul, add_sub_cancel]⟩) (fun a => by rw [Matrix.one_mulVec, h])
  simp only [Matrix.one_mulVec] at hex
  refine (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) y y' y').2.1 (hy'.trans (hpt.symm.trans hy.symm)) fun τ i =>
    ⟨(Pi.single i (1 : ℂ) : Fin (Dw.mult τ) → ℂ), ?_, fun j hj => Pi.single_eq_of_ne hj.ne' _, ?_⟩
  · rw [Pi.single_eq_same]
    exact isUnit_one (M := ℂ)
  · rw [hy]
    refine (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k P hP _ (y.u τ)
      (fun i => Pi.single (e.symm ⟨τ, i⟩) 1) (hu τ) _ (y'.u τ i)).2 ?_
    have d := hu' τ i
    simp only [hex] at d
    rw [Finset.sum_eq_single i (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp), Pi.single_eq_same,
      one_smul]
    exact d

set_option maxHeartbeats 1000000 in

theorem exists_dict_comp {D : D7} (V : HSp D) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (hr : V.rank = r)
    (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hσ : GoodEmb c σ) (hA : l.A = 1) (hpq : 1 ≤ Dw.p + Dw.q)
    (hU : IsUnf U) (hW : ∀ k, ModelW V hr (U.X k)) (hD : DictLat U V hr dict io e F ik φ th x₀)
    (hι : GlobalTheory.Member.IotaOK Dw V io) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ))
    (hx : ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
      gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
        Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (hdom : ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) (k : U.Comp) : ∃ h, (dict h).1 = k := by
  subst hr
  have hx₀ : ∀ k, IsOrthogonalFrame (U.X k) x₀ := fun k τ hτ => by
    rw [(hW k).1, (hU.2.1 k).1]
    exact hx τ (((hU.2.1 k).2 τ).1 hτ)
  have hty := (GlobalTheory.Relab.relab_good _ H l c σ hσ).2.2.2 Dw g e
  obtain ⟨x, hxd⟩ := GlobalTheory.Member.onto_dom_nonempty (U.X k)
  obtain ⟨h1, h4⟩ := GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E V.rank (U.X k).p0
    (U.X k).Ψ (U.X k).Gm (U.X k).Gm_herm
  obtain ⟨x₁, b, -, ho, -⟩ := h1 x hxd
  have hx₁d : x₁ ∈ (U.X k).dom := ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E V.rank (U.X k).p0
    (U.X k).Ψ (U.X k).Gm (U.X k).Gm_herm).2.1 x₁ ho).1
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hAr, -, hL⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V θ hθ
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have hmem : ∀ k (τ : D.host.E →+* ℂ), τ ∈ (U.X k).Ψ ↔ τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD := by
    intro k τ
    rw [(hU.2.1 k).2 τ, hι.rt, hι.rt0]
  have hex : ∀ τ : D.host.E →+* ℂ, ∃ u : Matrix (Fin V.rank) (Fin V.rank) ℂ, ∀ hτ : τ ∈ (U.X k).Ψ,
      uᵀ * (-V.gramᵀ).map τ * u.map (starRingEnd ℂ) = (-V.gramᵀ).map τ ∧ mat x₁ ⟨τ, hτ⟩ = u * x₀ τ := by
    intro τ
    by_cases hτ : τ ∈ (U.X k).Ψ
    · obtain ⟨u, hu⟩ := h4 τ (x₀ τ) (mat x₁ ⟨τ, hτ⟩) (hx₀ k τ hτ) ((ho ⟨τ, hτ⟩).trans (hx₀ k τ hτ).symm)
      rw [hG] at hu
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h' => absurd h' hτ⟩
  choose u hu using hex
  obtain ⟨a, ha, hau⟩ := hL u fun τ hτ => (hu τ ((hmem k τ).2 hτ)).1
  obtain ⟨h₀, hh₀⟩ := GlobalTheory.ShortMove.exists_marked_of_component D V H Dw l Xo _ g _ F hty _ rfl (U.X k) (ik k) (φ k) io
    (hW k) (hD.1.1 k) hι.emb hι.isom
  obtain ⟨a₀, ha₀, f, hf, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h₀
  have hfin : finHom V (a₀ * f) = finHom V (a * f) := by
    rw [map_mul, map_mul, show finHom V a₀ = 1 from ha₀, show finHom V a = 1 from ha]
  have hh : Marked V rfl io l (U.X k).Λ (fun a => (φ k (F.t (ik k) a) : Fin V.rank → D.host.E)) (a * f) := by
    obtain ⟨e₁, e₂⟩ := (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).2.1 _ _ hfin
    unfold Marked at hh₀ ⊢
    rwa [e₁, e₂, hfin] at hh₀
  refine ⟨a * f, ?_⟩
  obtain ⟨γ, hγ, hΛ, hm, hfr⟩ := hD.2 (a * f)
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix V γ hγ
  obtain ⟨gam, e₁, t₁, hgam⟩ := marked_isometry_half V l io (U.X k) (U.X (dict (a * f)).1) _ _ (φ k) (φ _) (F.t _) (F.t _)
    LinearMap.id (a * f) γ 1 (hW k) (hW _) (hD.1.1 k) (hD.1.1 _) δ hδu hδf rfl (fun a _ => ⟨0, zero_mem _, by
      rw [map_one, Units.val_one, Matrix.one_mulVec, smul_zero, add_zero]; rfl⟩) hh
    (by rw [mul_one]; exact ⟨hΛ, hm⟩)
  obtain ⟨P, hPe, hP, hy, hd⟩ := hD.1.2 k ⟨x₁, hx₁d⟩
  obtain ⟨P', hPe', hP', hy', hd'⟩ := hD.1.2 (dict (a * f)).1 ⟨_, hdom _⟩
  obtain ⟨_, -, _, -, hk⟩ := (hU.2.2.2.1 k (dict (a * f)).1 ⟨x₁, hx₁d⟩ ⟨_, hdom _⟩).1
    (frBor_of_isometry e F hpq hσ hA gam e₁ t₁ hP hP' (fun v => funext fun j => by
      rw [hPe, hPe', hgam]
      refine perFr_of_unitary _ _ (fun τ => by rw [hmem, hmem]) (by rw [hG, hG])
        (by rw [(hU.2.1 _).1, (hU.2.1 _).1]) (by rw [hG]; exact hδu) (fun τ h h' => ?_) _ _ _
      rw [hfr ⟨τ, h'⟩, GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth _ ⟨τ, h'⟩) (hθ τ), (hAr τ).2.1, (hAr τ).2.1,
        (hAr τ).2.2.1 f hf, hδa τ _ (hθ τ), hau τ ((hmem k τ).1 h), (hu τ h).2, Matrix.mul_one, ← Matrix.mul_assoc]
      rfl) _ _ hy hy' hd hd')
  exact congrArg Sigma.fst hk

open GlobalTheory.CoverRead GlobalTheory.Member in

theorem exists_dict₂_comp : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ k₂ : C.U₂.Comp, ∃ h : GA D (T.V j σ), (C.dict₂ h).1 = k₂ := by
  intro D T hT j hj σ hσ C hC k₂
  obtain ⟨-, hA, hinc, hU, hdom, hr, g, e, F, ik, φ, th, hW, hth, hD⟩ := hC
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT j hj σ hσ _ rfl hr
  have hpq := (exists_iotaOK D T.Q hT.pins _ hj).2
  have hσ₂ : GoodEmb C.d.c₂ C.σ₂ := by
    rw [← hinc] at hσ
    exact hσ
  exact exists_dict_comp _ hr C.U₂ C.dict₂ _ e F ik φ th _ hσ₂ hA (by omega) hU hW hD hio hth hx₀ hdom k₂

end GlobalTheory.CoverOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspCoefficient
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.ThetaSumDescent

theorem exists_cusp_thetaSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), 1 ≤ r → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → l.A = 1 → ∀ [StarRing (𝓞 E)] (a : (E →+* ℂ) × ℕ → ℕ) (n N : ℕ) (dδ : DeltaDat Xo c n) (La : GenLat E n) (T : Type) [Fintype T] (cs : T → Rul dδ.Xo₂ dδ.c₂) (e : ℕ) (w : T → (Fin n → LevQ Dw dδ.l₂) → c.F) (P : T → MvPolynomial (LtN Dw n) c.F), Dom a n → LastPos Dw a → dδ.IsLev → dδ.l₂.A = 1 → IsNab dδ.Xo₂ dδ.c₂ dδ.nab₂ → La.Unimod → La.TrivAt dδ.l₂.M → La.LevOK N dδ.l₂.M → 0 < e → (∀ t, cs t ∈ sec dδ.Xo₂ dδ.c₂ 0 0 ∧ cs t ^ (e + 1) = cs t) → (∀ t, P t ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → SumInv dδ cs w P → ∃ f ∈ cusp Xo c U a n, (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k], (∀ x : c.F, algebraMap dδ.c₂.F k (dδ.eF x) = algebraMap c.F k x) → ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y → ∃ v : T → k, (∀ t, thLaValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (fun q => dδ.eF (w t q)) La N (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (P t)) y₂ (v t)) ∧ evR Xo c f y = ∑ t, evR dδ.Xo₂ dδ.c₂ (cs t) y₂ * v t) ∧ ∀ f' ∈ sec Xo c a n, (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k], (∀ x : c.F, algebraMap dδ.c₂.F k (dδ.eF x) = algebraMap c.F k x) → ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y → ∃ v : T → k, (∀ t, thLaValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (fun q => dδ.eF (w t q)) La N (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (P t)) y₂ (v t)) ∧ evR Xo c f' y = ∑ t, evR dδ.Xo₂ dδ.c₂ (cs t) y₂ * v t) → f' = f := by
  intro E _ _ _ H Dw l Xo c r U hr hU hA _ a n N d La T _ cs e w P hD hL hlev hA₂ hnab hun hT hO he hcs hP hinv
  obtain ⟨f, hf, hval⟩ := exists_sec_thetaSum d hlev hnab La N hun hT hO a cs w P (fun t => (hcs t).1) hP hinv
  refine ⟨f, ?_, hval, fun f' hf' hval' => ?_⟩
  · rw [← Formalism.L2.PjFree.cusp_ofPj]
    exact mem_cusp_of_thetaSum d (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) hr
      (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 (hU σ hσ)) hA hlev hA₂ hnab La N hun hT hO a hD hL cs e he w P hcs hP
      f hf hval
  · refine GlobalTheory.ClassSumUnique.sec_eq_of_geometric hf' hf fun k _ _ _ y => ?_
    letI : Algebra d.c₂.F k := ((algebraMap c.F k).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
    have hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a => by
      show algebraMap c.F k (d.eF.symm (d.eF a)) = _
      rw [AlgEquiv.symm_apply_apply]
    obtain ⟨y₂, hy⟩ := hlev.2.2.2.2.2.2.1 k hk y
    obtain ⟨v, hv, e₁⟩ := hval k hk y y₂ hy
    obtain ⟨v', hv', e₂⟩ := hval' k hk y y₂ hy
    rw [e₁, e₂]
    unfold thLaValAt at hv hv'
    exact sum_values_eq d.nab₂ hnab La N hun hT hO a _
      (fun t => (GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a _ (hP t)) _ _ 1 y₂ _ _ _ _ hv hv' fun _ _ => rfl

section Shift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} {A : Type} [AddCommGroup A]

def ShiftTie (d : DeltaDat Xo c n) (cs : A → Rul d.Xo₂ d.c₂) (κ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) → A) : Prop :=
  ∀ (k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (s : Sim Dw) (ρ : d.Xo₂.X ≅ d.Xo₂.X), s.InGam l d.l₂ → d.Xo₂.LevAut s ρ →
    (∀ x : Dw.La, (Submodule.Quotient.mk (s.f d.l₂.M x) : LaI Xo c d) = k (Submodule.Quotient.mk x)) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra d.c₂.F K] (y y' : FrPt d.Xo₂ d.c₂ K), y'.x = y.x ≫ ρ.hom →
      ∀ a, evR d.Xo₂ d.c₂ (cs (a + κ k)) y' = evR d.Xo₂ d.c₂ (cs a) y

def ShiftEq (d : DeltaDat Xo c n) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ)
    (κ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) → A) (φ : A → (Fin n → LevQc Dw d.l₂) → c.F) : Prop :=
  ∀ (k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (σq : LevQ Dw d.l₂ ≃ₗ[𝓞 E] LevQ Dw d.l₂)
    (σc : LevQc Dw d.l₂ ≃ₗ[𝓞 E] LevQc Dw d.l₂),
    (∀ x y : Dw.La, σq (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
      x - y ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ∧ k (Submodule.Quotient.mk x) = Submodule.Quotient.mk y) →
    (∀ (x : LevQc Dw d.l₂) (q : LevQ Dw d.l₂), (d.l₂.M : ℤ) ∣
      Dw.EF (qRep (σc x)) (cSep d.l₂ • levRep (σq q)) - Dw.EF (qRep x) (cSep d.l₂ • levRep q)) →
    ∀ a x, φ a (fun b => σc.symm (x b)) = (((ψ k)⁻¹ : c.Fˣ) : c.F) * φ (a + κ k) x

end Shift

section Marks

open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Member
open scoped TensorProduct

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} {A : Type} [AddCommGroup A] [DecidableEq A]

end Marks

end GlobalTheory.ThetaSumDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldExtensionOfIntegralRetraction
section
open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc

noncomputable section

namespace GlobalTheory.UseLoc.ExtRet

variable {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l}

theorem algebraMap_ne_zero (LL : FinExt l) {d : ℤ_[l]} (hd : d ≠ 0) : algebraMap ℤ_[l] LL.1 d ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] LL.1]
  intro h0
  apply hd
  have h1 : algebraMap ℤ_[l] ℚ_[l] d = 0 := (map_eq_zero_iff _ (algebraMap ℚ_[l] LL.1).injective).1 h0
  exact (map_eq_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).1 h1

theorem exists_mul (LL : FinExt l) (x : LL.1) : ∃ d : ℤ_[l], d ≠ 0 ∧ IsIntegral ℤ_[l] (d • x) := by
  haveI := LL.2
  haveI : Algebra.IsAlgebraic ℤ_[l] LL.1 :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ_[l]) (K := ℚ_[l]) (C := LL.1)).2 inferInstance
  exact (Algebra.IsAlgebraic.isAlgebraic x).exists_integral_multiple

theorem r_smul (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (c : ℤ_[l]) (z : ↥(OL LL')) :
    ((r (c • z) : ↥(OL LL)) : LL.1) = algebraMap ℤ_[l] LL.1 c * ((r z : ↥(OL LL)) : LL.1) := by
  have e : c • z = incO h (algebraMap ℤ_[l] (OL LL) c) * z := by
    apply Subtype.ext
    simp [incO, Algebra.smul_def]
  rw [e, hr]
  simp

def ext (r : ↥(OL LL') →+ ↥(OL LL)) (x : LL'.1) : LL.1 :=
  ((r ⟨(exists_mul LL' x).choose • x, (exists_mul LL' x).choose_spec.2⟩ : ↥(OL LL)) : LL.1) /
    algebraMap ℤ_[l] LL.1 (exists_mul LL' x).choose

theorem ext_eq (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x)
    (x : LL'.1) (d : ℤ_[l]) (hd : d ≠ 0) (y : ↥(OL LL')) (hy : (y : LL'.1) = d • x) :
    ext r x = ((r y : ↥(OL LL)) : LL.1) / algebraMap ℤ_[l] LL.1 d := by
  unfold ext
  set d0 := (exists_mul LL' x).choose with hd0def
  have hd0 : d0 ≠ 0 := (exists_mul LL' x).choose_spec.1
  set y0 : ↥(OL LL') := ⟨d0 • x, (exists_mul LL' x).choose_spec.2⟩ with hy0
  have key : d • y0 = d0 • y := by
    apply Subtype.ext
    simp only [SetLike.val_smul, hy0, hy, smul_smul, mul_comm]
  have k2 := congrArg (fun z => ((r z : ↥(OL LL)) : LL.1)) key
  simp only [r_smul h r hr] at k2
  rw [div_eq_div_iff (algebraMap_ne_zero LL hd0) (algebraMap_ne_zero LL hd)]
  linear_combination k2

theorem ext_add (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (x₁ x₂ : LL'.1) :
    ext r (x₁ + x₂) = ext r x₁ + ext r x₂ := by
  obtain ⟨d₁, hd₁, hi₁⟩ := exists_mul LL' x₁
  obtain ⟨d₂, hd₂, hi₂⟩ := exists_mul LL' x₂
  let y₁ : ↥(OL LL') := ⟨d₁ • x₁, hi₁⟩
  let y₂ : ↥(OL LL') := ⟨d₂ • x₂, hi₂⟩
  have hy : ((d₂ • y₁ + d₁ • y₂ : ↥(OL LL')) : LL'.1) = (d₁ * d₂) • (x₁ + x₂) := by
    simp only [y₁, y₂, Subalgebra.coe_add, SetLike.val_smul, smul_smul, smul_add]
    rw [mul_comm d₂ d₁]
  rw [ext_eq h r hr _ (d₁ * d₂) (mul_ne_zero hd₁ hd₂) _ hy, ext_eq h r hr x₁ d₁ hd₁ y₁ rfl,
    ext_eq h r hr x₂ d₂ hd₂ y₂ rfl, map_add, Subalgebra.coe_add, r_smul h r hr, r_smul h r hr, map_mul]
  have n₁ := algebraMap_ne_zero LL hd₁
  have n₂ := algebraMap_ne_zero LL hd₂
  field_simp

theorem ext_mul (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (a : LL.1) (x : LL'.1) :
    ext r (IntermediateField.inclusion h a * x) = a * ext r x := by
  obtain ⟨d, hd, hi⟩ := exists_mul LL' x
  obtain ⟨e, he, hie⟩ := exists_mul LL a
  let y : ↥(OL LL') := ⟨d • x, hi⟩
  let a'' : ↥(OL LL) := ⟨e • a, hie⟩
  have hy : ((incO h a'' * y : ↥(OL LL')) : LL'.1) = (e * d) • (IntermediateField.inclusion h a * x) := by
    simp only [incO, y, a'', RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Subalgebra.coe_mul,
      SetLike.val_smul, map_smul]
    simp only [Algebra.smul_def, map_mul]
    have hc : IntermediateField.inclusion h (algebraMap ℤ_[l] LL.1 e) = algebraMap ℤ_[l] LL'.1 e := by simp
    rw [hc]
    ring
  rw [ext_eq h r hr _ (e * d) (mul_ne_zero he hd) _ hy, ext_eq h r hr x d hd y rfl, hr,
    Subalgebra.coe_mul, map_mul]
  have n₁ := algebraMap_ne_zero LL hd
  have n₂ := algebraMap_ne_zero LL he
  have ha : ((a'' : ↥(OL LL)) : LL.1) = algebraMap ℤ_[l] LL.1 e * a := by
    simp [a'', Algebra.smul_def]
  rw [ha]
  field_simp

theorem ext_int (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (x : ↥(OL LL')) :
    ext r (x : LL'.1) = ((r x : ↥(OL LL)) : LL.1) := by
  rw [ext_eq h r hr _ 1 one_ne_zero x (by simp)]
  simp

end GlobalTheory.UseLoc.ExtRet

namespace GlobalTheory.UseLoc

theorem extRet_exists : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL)), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) → r 1 = 1 → ∃ p : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ (a : ↥LL.1) (x : ↥LL'.1), p (IntermediateField.inclusion h a * x) = a * p x) ∧ ∀ x : ↥(OL LL'), p (x : ↥LL'.1) = ((r x : ↥(OL LL)) : ↥LL.1) := by
  intro l _ LL LL' h r hr _
  refine ⟨{ toFun := ExtRet.ext r
            map_add' := ExtRet.ext_add h r hr
            map_smul' := fun q x => ?_ }, ExtRet.ext_mul h r hr, ExtRet.ext_int h r hr⟩
  have e : q • x = IntermediateField.inclusion h (algebraMap ℚ_[l] LL.1 q) * x := by
    rw [Algebra.smul_def]
    rfl
  simp only [RingHom.id_apply]
  rw [e, ExtRet.ext_mul h r hr, Algebra.smul_def]

end GlobalTheory.UseLoc
end
end

