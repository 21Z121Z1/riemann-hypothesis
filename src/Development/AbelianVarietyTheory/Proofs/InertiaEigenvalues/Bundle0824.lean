import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0814
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0816
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyAlgHomOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0691
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0817
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0818
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0813

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameKeepsMatricesSplitPlaceReductionLocal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.MtRead.Red

section General

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem ALint_eq : ReciprocityTheory.Aut.ALint L = Formalism.L2.Herm.intAf (maximalRealSubfield L) L := by
  apply le_antisymm
  · refine Subring.closure_le.2 ?_
    rintro z (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨⟨(y : L), ⟨y, rfl⟩⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  · refine Subring.closure_le.2 ?_
    rintro x (⟨⟨_, y, rfl⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨y, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨c, hc, rfl⟩)

theorem proj_tmul_one (s : ReciprocityTheory.Aut.SplitPlace L) (y : L) :
    s.proj (y ⊗ₜ[maximalRealSubfield L] (1 : ReciprocityTheory.Aut.AFplus L)) = s.i y := by
  simp [ReciprocityTheory.Aut.SplitPlace.proj, Algebra.TensorProduct.lift_tmul]

theorem proj_mem (s : ReciprocityTheory.Aut.SplitPlace L) {z : ReciprocityTheory.Aut.AL L} (hz : z ∈ ReciprocityTheory.Aut.ALint L) :
    s.proj z ∈ s.v.adicCompletionIntegers (maximalRealSubfield L) := by
  have hle : ReciprocityTheory.Aut.ALint L ≤ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring.comap s.proj := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨y, rfl⟩ | ⟨c, hc, rfl⟩)
    · show s.proj _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield L)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, proj_tmul_one]
      exact s.split_le_one y
    · show s.proj _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield L)
      simp only [ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul,
        map_one, one_mul]
      exact hc s.v
  exact hle hz

theorem proj_lt_one (s : ReciprocityTheory.Aut.SplitPlace L) (z : Formalism.L2.Herm.intAf (maximalRealSubfield L) L)
    (hz : z ∈ Formalism.L2.DIV.idS (maximalRealSubfield L) s.w.asIdeal) :
    Valued.v (s.proj (z : ReciprocityTheory.Aut.AL L)) < 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Formalism.L2.DIV.oToS_coe, proj_tmul_one]
    exact hy
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul c x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    have hc : Valued.v (s.proj (c : ReciprocityTheory.Aut.AL L)) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (proj_mem s ((ALint_eq (L := L)).ge c.2))
    calc Valued.v (s.proj (c : ReciprocityTheory.Aut.AL L)) * Valued.v (s.proj (x : ReciprocityTheory.Aut.AL L))
        ≤ 1 * Valued.v (s.proj (x : ReciprocityTheory.Aut.AL L)) := by gcongr
      _ < 1 := by rwa [one_mul]

theorem resS_iff (s : ReciprocityTheory.Aut.SplitPlace L) (z : Formalism.L2.Herm.intAf (maximalRealSubfield L) L) (u : 𝓞 L) :
    Valued.v (s.i (u : L) - s.proj (z : ReciprocityTheory.Aut.AL L)) < 1 ↔
      Formalism.L2.DIV.resS (maximalRealSubfield L) s.w z = Ideal.Quotient.mk s.w.asIdeal u := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (Formalism.L2.DIV.resS (maximalRealSubfield L) s.w z)
  have e1 : Formalism.L2.DIV.cmpS (maximalRealSubfield L) s.w.asIdeal (Formalism.L2.DIV.resS (maximalRealSubfield L) s.w z) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS (maximalRealSubfield L) s.w.asIdeal) z :=
    (RingEquiv.ofBijective (Formalism.L2.DIV.cmpS (maximalRealSubfield L) s.w.asIdeal)
      (Formalism.L2.DIV.cmpS_bij (F := maximalRealSubfield L) s.w.asIdeal s.w.ne_bot)).apply_symm_apply _
  have e2 : Formalism.L2.DIV.cmpS (maximalRealSubfield L) s.w.asIdeal (Ideal.Quotient.mk s.w.asIdeal b) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS (maximalRealSubfield L) s.w.asIdeal) (Formalism.L2.DIV.oToS (maximalRealSubfield L) L b) :=
    Ideal.quotientMap_mk
  have hmem : z - Formalism.L2.DIV.oToS (maximalRealSubfield L) L b ∈ Formalism.L2.DIV.idS (maximalRealSubfield L) s.w.asIdeal := by
    refine Ideal.Quotient.eq.1 ?_
    exact e1.symm.trans ((congrArg (Formalism.L2.DIV.cmpS (maximalRealSubfield L) s.w.asIdeal) hb.symm).trans e2)
  have h1 : Valued.v (s.proj (z : ReciprocityTheory.Aut.AL L) - s.i (algebraMap (𝓞 L) L b)) < 1 := by
    have := proj_lt_one s _ hmem
    rwa [AddSubgroupClass.coe_sub, map_sub, Formalism.L2.DIV.oToS_coe, proj_tmul_one] at this
  rw [← hb, eq_comm (a := Ideal.Quotient.mk s.w.asIdeal b), Ideal.Quotient.eq]
  show _ ↔ Valued.v (s.i ((u - b : 𝓞 L) : L)) < 1
  have e : s.i ((u - b : 𝓞 L) : L) =
      (s.i (u : L) - s.proj (z : ReciprocityTheory.Aut.AL L)) + (s.proj (z : ReciprocityTheory.Aut.AL L) - s.i (algebraMap (𝓞 L) L b)) := by
    simp only [RingOfIntegers.coe_eq_algebraMap, map_sub]
    ring
  constructor
  · intro h
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h h1)
  · intro h
    rw [← sub_eq_iff_eq_add] at e
    rw [← e]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h h1)

def castE {F : Subfield L} (h : F = maximalRealSubfield L) :
    ReciprocityTheory.Aut.AL L ≃+* L ⊗[F] FiniteAdeleRing (𝓞 F) F :=
  (GlobalTheory.Mem.R3.swapCast h).symm.trans (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) L).toRingEquiv

theorem castE_rfl (x : ReciprocityTheory.Aut.AL L) : castE (L := L) rfl x = x :=
  (Algebra.TensorProduct.comm (maximalRealSubfield L) (ReciprocityTheory.Aut.AFplus L) L).apply_symm_apply x

theorem castE_mem_iff {F : Subfield L} (h : F = maximalRealSubfield L) (x : ReciprocityTheory.Aut.AL L) :
    castE h x ∈ Formalism.L2.Herm.intAf F L ↔ x ∈ ReciprocityTheory.Aut.ALint L := by
  subst h
  rw [castE_rfl, ALint_eq]

theorem resS_castE_iff {F : Subfield L} (h : F = maximalRealSubfield L) (s : ReciprocityTheory.Aut.SplitPlace L) (x : ReciprocityTheory.Aut.AL L)
    (z : Formalism.L2.Herm.intAf F L) (hz : (z : L ⊗[F] FiniteAdeleRing (𝓞 F) F) = castE h x) (u : 𝓞 L) :
    Valued.v (s.i (u : L) - s.proj x) < 1 ↔ Formalism.L2.DIV.resS F s.w z = Ideal.Quotient.mk s.w.asIdeal u := by
  subst h
  rw [castE_rfl] at hz
  rw [← hz]
  exact resS_iff s z u

end General

section Stab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m : ℕ}

theorem frGL_one_val (y : GL (Fin m) (Formalism.L2.Herm.intAf F E)) (a c : Fin m) :
    (frGL (1 : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) y).val a c = (y.val a c : E ⊗[F] Formalism.L2.Herm.Af F) := by
  have h : frGL (1 : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) y = intGL F E m y := by
    simp [frGL]
  rw [h]
  rfl

theorem mem_St_one (g : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) (h : ∀ a c, g.val a c ∈ Formalism.L2.Herm.intAf F E)
    (h' : ∀ a c, (g⁻¹).val a c ∈ Formalism.L2.Herm.intAf F E) : g ∈ St (1 : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  have inj : Function.Injective ((Formalism.L2.Herm.intAf F E).subtype.mapMatrix (m := Fin m)) :=
    fun x y hxy => Matrix.ext fun a c => Subtype.ext (congrFun (congrFun hxy a) c)
  refine ⟨⟨Matrix.of fun a c => ⟨_, h a c⟩, Matrix.of fun a c => ⟨_, h' a c⟩, inj ?_, inj ?_⟩, ?_⟩
  · rw [map_mul, map_one]
    exact g.mul_inv
  · rw [map_mul, map_one]
    exact g.inv_mul
  · refine Units.ext (Matrix.ext fun a c => ?_)
    rw [frGL_one_val]
    rfl

end Stab

theorem red_eq_local : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n), IdFrame hF P → ∀ (hn : V.rank = n) (κ : GAf D.host.E n), (κ ∈ ReciprocityTheory.Aut.Umax D.host.E n ↔ Lev.finE V (P.ψ κ) ∈ St (1 : GL (Fin V.rank) (Lev.EAf D))) ∧ ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, κ ∈ ReciprocityTheory.Aut.Umax D.host.E n → ∀ a c : Fin V.rank, NX.locM s κ (Fin.cast hn a) (Fin.cast hn c) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) ∧ ∀ u : 𝓞 D.host.E, Valued.v (s.i (u : D.host.E) - NX.locM s κ (Fin.cast hn a) (Fin.cast hn c)) < 1 ↔ (redFn (1 : GL (Fin V.rank) (Lev.EAf D)) s.w (Lev.finE V (P.ψ κ))).val a c = Ideal.Quotient.mk s.w.asIdeal u := by
  intro D V n hF P hP hn κ
  obtain ⟨hn', hP⟩ := hP
  have ent : ∀ (κ : GAf D.host.E n) a c, (Lev.finE V (P.ψ κ)).val a c =
      castE hF ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn c)) := fun κ a c =>
    congrArg (Lev.swapAE D) (hP κ a c)
  have toSt : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n → Lev.finE V (P.ψ κ) ∈ St (1 : GL (Fin V.rank) (Lev.EAf D)) := fun hκ => by
    refine mem_St_one _ (fun a c => ?_) (fun a c => ?_)
    · rw [ent]
      exact (castE_mem_iff hF _).2 (hκ _ _)
    · rw [← map_inv, ← map_inv, ent]
      exact (castE_mem_iff hF _).2 (Subgroup.inv_mem _ hκ _ _)
  refine ⟨⟨toSt, ?_⟩, fun s hκ a c => ⟨proj_mem s (hκ _ _), fun u => ?_⟩⟩
  · rintro ⟨y, hy⟩ i j
    have h1 := ent κ (Fin.cast hn.symm i) (Fin.cast hn.symm j)
    rw [← hy, frGL_one_val] at h1
    exact (castE_mem_iff hF _).1 (h1 ▸ (y.val _ _).2)
  · obtain ⟨y, hy⟩ := toSt hκ
    have h1 := ent κ a c
    rw [← hy, frGL_one_val] at h1
    rw [← hy, redFn_frGL]
    exact resS_castE_iff hF s _ (y.val a c) h1 u

end GlobalTheory.MtRead.Red

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPartProjectorSpectralAtEveryLocalisationStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_part_projector_spectral_at_every_localisation : ∀ (D : D7) (M : MtFam D), HeckeTied D M → HeckeRational D M → AVTied D M → ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → (∀ i : D.nd.Loc, ClassSum (M.loc i)) → (∀ i : D.nd.Loc, ThetaCut D (D.nd.mu i) (D.nd.j i)) → D.nd.EigSpan → Rows.IsotInternal D.what₂ → SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → GoodFTAll D → ∀ i, SpecPr D i := by
  first | exact @GlobalTheory.EtaJoin.SpecAll.specPr_all | exact GlobalTheory.EtaJoin.SpecAll.specPr_all | (intros; apply GlobalTheory.EtaJoin.SpecAll.specPr_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypeFormReadingRightTranslateLiftStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_type_form_reading_right_translate_lift : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b, ∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (κ : GA D (Wc D j)),
      Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b u) κ → ∀ g,
      Y.Z.rd i j b x (g * κ) = Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) *
        Y.Z.rd i j b x g := by
  first | exact @GlobalTheory.TypeRead.rd_mul_lift | exact GlobalTheory.TypeRead.rd_mul_lift | (intros; apply GlobalTheory.TypeRead.rd_mul_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolysReachSmallFieldCoefficientFunctionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_polys_reach_small_field_coefficient_functions : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b (F : VV ↥D.LL0 (Y.Z.ρ.B i j b).w.lam), ∃ P ∈ (Y.Z.ρ.B i j b).valSpace, harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P = coefFn (Formalism.L2.Host.embLL0 D) (Y.Z.ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) := by
  first | exact @GlobalTheory.IntExpOnto.onto | exact GlobalTheory.IntExpOnto.onto | (intros; apply GlobalTheory.IntExpOnto.onto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeReadOfDeltaFrob
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TwInputs.HeckePinRead

theorem pull_locE {D : D7} {Ω : Type} [Field Ω] [Algebra D.host.E Ω] {A : Type} [CommGroup A] (a : Recip D Ω) (ha : a.Good)
    (φ : G D.host.E Ω →* A) (hφ : IsOpen (φ.ker : Set (G D.host.E Ω))) (P : Pl D.host.E) (e : AE D)
    (he : Formalism.L2.JoinChr.IsPlIdem D e P) (k : D.host.Eˣ)
    (hk : Valued.v ((Formalism.L2.Host.atFin P k : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) = WithZero.exp (-1 : ℤ))
    (x : (AE D)ˣ) (hx : (x : AE D) = Formalism.L2.JoinChr.locE D e (k : D.host.E)) (B : ValuationSubring Ω)
    (hB : IsPlaceOver (F := D.host.E) B P) (hine : ∀ τ ∈ Ine (F := D.host.E) B, φ τ = 1) (σ : G D.host.E Ω)
    (hσ : IsFrob (F := D.host.E) B (normV P) σ) : a.pull φ x = (φ σ)⁻¹ := by
  have hκ : a.κ (x : AE D) = ((Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k) : Neutral.B1.Ideles D.host.E) :
      AdeleRing (𝓞 D.host.E) D.host.E) := by
    rw [hx]; exact ha.loc P e he k
  have hsym : a.sym x = a.art (Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k)) := by
    rw [Recip.sym, MonoidHom.comp_apply]
    congr 1
    exact Units.ext hκ
  obtain ⟨y, hy, hyσ⟩ := (ha.artin.frob P B hB _).mpr ⟨σ, hσ, rfl⟩
  have hu : Valued.v (((Formalism.L2.Host.atFin P k * y⁻¹ : (P.adicCompletion D.host.E)ˣ)) : P.adicCompletion D.host.E) = 1 := by
    have hy' : Valued.v ((y : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) = WithZero.exp (-1 : ℤ) := hy
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hk, hy']
    exact mul_inv_cancel₀ WithZero.exp_ne_zero
  obtain ⟨τ, hτ, hτu⟩ := (ha.artin.ine P B hB _).mp ⟨_, hu, rfl⟩
  have hs : a.sym x = GlobalTheory.HeckeGal.toAb D.host.E Ω (τ * σ⁻¹) := by
    rw [hsym, show Formalism.L2.Host.atFin P k = (Formalism.L2.Host.atFin P k * y⁻¹) * y by group, map_mul, map_mul, hyσ,
      ← hτu, map_mul]
  rw [a.pull_eq hφ hs, map_mul, hine τ hτ, map_inv, one_mul]

theorem isOpen_ker_psiAt (D : D7) (i : D.ntw.Tw) (b : Bool) :
    IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
  have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
    ext g
    cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
  rw [e]
  exact D.ntw.delta_open i

theorem chi_locU_unif {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (P : PlE D.host)
    (hP : P ∉ D.ntw.S0 i) {e : AE D} (he : Formalism.L2.JoinChr.IsPlIdem D e P) (hee : e * e = e) (σ : G D.host.E D.nd.Om)
    (hσ : IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ) :
    (((ρ.B i j b).de.chi (Formalism.L2.JoinChr.locU hee (Formalism.L2.Host.unif P)) : Circle) : ℂ) =
      (ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)))⁻¹ := by
  rw [hρ.delta i j b]
  have hopen := isOpen_ker_psiAt D i b
  have : Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ⁻¹ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ⁻¹)
  have hine : ∀ τ ∈ Ine (F := D.host.E) (D.nd.plOm.1 P), Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) τ = 1 := by
    intro τ hτ
    have h : D.ntw.delta i τ = 1 := by
      by_contra hne
      exact hP (D.ntw.primes_subset_exceptional i ((D.ntw.delta_ram i P _ (D.nd.plOm.2 P)).1 ⟨τ, hτ, hne⟩))
    cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, h]
  have hpull := pull_locE ρ.rc hρ.rc _ hopen P e he (Formalism.L2.Host.unif P) (Formalism.L2.Host.unif_spec P) _
    (Formalism.L2.JoinChr.locU_val hee _) _ (D.nd.plOm.2 P) hine σ hσ
  change ((charOf ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)))
    (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) _ : Circle) : ℂ) = _
  rw [charOf, MonoidHom.comp_apply, MonoidHom.comp_apply, hpull, unitPart_of_pow hn]
  · simp
  · rw [← map_pow, ← map_inv, ← map_pow, map_pow (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)), hpow, map_one]

def frobU (D : D7) (P : PlE D.host) : G D.host.E D.nd.Om :=
  (GlobalTheory.TripleGal.exists_mem_Dec_isFrob D P (D.nd.plOm.1 P) (D.nd.plOm.2 P)).choose

theorem frobU_spec (D : D7) (P : PlE D.host) : IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) (frobU D P) :=
  (GlobalTheory.TripleGal.exists_mem_Dec_isFrob D P (D.nd.plOm.1 P) (D.nd.plOm.2 P)).choose_spec.2

def uD (D : D7) : ∀ i : D.ntw.Tw, Bool → PlE D.host → (D.ntw.O i)ˣ := fun i b P =>
  Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) (frobU D P))

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}

theorem isDeltaInv_uD {D : D7} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (hρ : ρ.Good)
    (hpin : RealPin Rl cG ρ) : IsDeltaInv ρ (uD D) := by
  intro i j b k P hk α z hα hz
  obtain ⟨-, -, hsp, hP⟩ := hk
  have hdQ : Bridge.SplitOff P (((ρ.B i j b).de.Q : Finset _) : Set (Pl D.host.E)) :=
    GlobalTheory.SplitOffS0.main hρ i _ (fun P' hP' => by
      rw [hρ.delta i j b] at hP'
      exact D.ntw.primes_subset_exceptional i (mem_half.1 hP').1) P hsp hP
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P hdQ.1
  have hee : e * e = e := he.1.1
  have h1 := (hpin.delta i j b).2 P e (GlobalTheory.HeckeDetChar.isPlIdem he) (Formalism.L2.Host.unif P) _
    (Formalism.L2.JoinChr.locU_val hee (Formalism.L2.Host.unif P))
  have h2 := chi_locU_unif hρ i j b P hP (GlobalTheory.HeckeDetChar.isPlIdem he) hee (frobU D P) (frobU_spec D P)
  rw [GlobalTheory.HeckeDetChar.chi_detAt (hpin.delta i j b) (hρ.base i j b).de.unram (hρ.base i j b).de.split hdQ hα hz,
    show (((Rl.C.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ) = (((ρ.B i j b).de.chi (Formalism.L2.JoinChr.locU hee (Formalism.L2.Host.unif P)) : Circle) : ℂ)
      from h1.symm, h2, inv_pow, inv_inv]
  rfl

end GlobalTheory.TwInputs.HeckePinRead

namespace GlobalTheory.TwInputs

end GlobalTheory.TwInputs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertSatakeParametersAgreeUnderDictionaryStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_satake_parameters_agree_under_dictionary : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → (π.SphAt v → IsUnramU U w) ∧ ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → (∃ Dv : InertDatum L n v w, Dv.σw = s ∧ Dv.ϖ = ϖ) ∧ ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), Dv.σw = s → Dv.ϖ = ϖ → NG.SatAt π Dv α → ∃ α' : Fin (n / 2) → ℂˣ, (∀ i, (α' i : ℂ) = α i) ∧ HasSatAt U w s ϖ q α' := by
  first | exact @GlobalTheory.InertDict.satake_agree | exact GlobalTheory.InertDict.satake_agree | (intros; apply GlobalTheory.InertDict.satake_agree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvPlaceNormProductMemCoefficientRingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_place_norm_product_mem_coefficient_ring : ∀ (D : D7) (ρ : Setup D.ntw) (i : D.ntw.Tw) (b : Bool) (Q : Finset (Pl D.host.E)), Disjoint Q (D.ntw.S0 i) → ((normProd Q : ℕ) : ℂ)⁻¹ ∈ (ρ.eO i b).range := by
  first | exact @GlobalTheory.NormUnit.normProd_inv_mem | exact GlobalTheory.NormUnit.normProd_inv_mem | (intros; apply GlobalTheory.NormUnit.normProd_inv_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

def flipIdx (V W : HSp D) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) : ℕ :=
  ∏ PP ∈ T, Ideal.absNorm (PP.maxPowDividing (Ideal.span {((m : ℕ) : 𝓞 D.host.E)})) ^ (V.rank * W.rank)

def flipScal (χW : (AE D)ˣ →* Circle) (V W : HSp D) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (x : (AE D)ˣ) : ℂ :=
  ((χW x : Circle) : ℂ)⁻¹ * ((Real.sqrt (flipIdx V W T m : ℝ) : ℝ) : ℂ)⁻¹

def IsFlipDet (V : HSp D) (e : AE D) (m : ℕ) (x : (AE D)ˣ) : Prop :=
  (x : AE D) * (e * (m : AE D) ^ V.rank + (1 - e)) = 1

end GlobalTheory.LevelSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelsOfDepthZeroStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.labels_of_depth_zero : Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : ∀ k, LabelDatum (D.host.g k)), GlobalTheory.HeightCounting.RowTrue hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → LabTie D L → (∀ k, TameGen.DepthZeroCuspidal (D.host.g k)) → (∀ (I : Ident D) rc, IsRc hL T I rc → ∀ k v, TameGen.TameParam (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v)) (fun π : Supp.GLRep _ => rc k v π.1 π.2)) → (∀ (I : Ident D) cp, IsComp I rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g D.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ a, ρ.asAlgebraHom a x ∈ W) ∧ ρ.asAlgebraHom D.ntypes.e0 x = x) → GoodFTAll D := by
  first | exact @GlobalTheory.GoodAll.goodFTAll_of_local | exact GlobalTheory.GoodAll.goodFTAll_of_local | (intros; apply GlobalTheory.GoodAll.goodFTAll_of_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftWeightInfinitesimalCharacterEqDefiniteParamStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_weight_infinitesimal_character_eq_definite_param : ∀ (D : D7) (j : Fin D.R.m) (hn : (Vc D j).rank = D.R.nV) (t : D.what₂.Tau), NG.infOf (fun a : Fin D.R.nV => (FWT.lamV D j t).w (Fin.cast hn.symm a)) = NG.paramV D.R (D.hc t) j (1 / 2) := by
  first | exact @GlobalTheory.InertiaEigenvalues.LamParam.infOf_lamV_eq_paramV | exact GlobalTheory.InertiaEigenvalues.LamParam.infOf_lamV_eq_paramV | (intros; apply GlobalTheory.InertiaEigenvalues.LamParam.infOf_lamV_eq_paramV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingTheoremWachModuleLemmaHypothesesAdmittedStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftingTheorem_wachModuleLemma_hypotheses_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), LiftingTheory.admitted D HW F Cm ∧ CrystallineLiftingBounds.admitted D HW F Cm := by
  first | exact @GlobalTheory.LiftAdmitted.all_admitted | exact GlobalTheory.LiftAdmitted.all_admitted | (intros; apply GlobalTheory.LiftAdmitted.all_admitted <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglandsBridge

theorem localLanglandsGL_of_depthZero_zelevinsky_bernstein : LocalLanglandsExists → LocalConverseGL → DepthZeroCuspidalLL → DepthZeroInduction →
    BrauerDegreeZero → ChevalleyUnits → GlobalArtinReciprocity → LanglandsExhaustionGL → LanglandsMultisegments →
    StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → LocalLanglandsGL := by
  intro hEx hConv hDep hInd hBr hChev hArt hExh hMult hCos hZel hGeo hBZ
  have hRec := GlobalTheory.T.rec_of_rec_literal hDep hInd hExh hMult hCos hZel hGeo hBZ
  have hComp := GlobalTheory.T.local_langlands_transport hArt hChev hBr hEx hConv hExh hBZ
  refine ⟨?_, ?_⟩
  · intro E Ω _ _ _ _ _ A w h
    obtain ⟨rc, hrc⟩ := hEx E Ω A w h
    refine ⟨rc, hRec E Ω A w h rc hrc, ?_⟩
    intro rc' hrc'
    funext x
    obtain ⟨n, c⟩ := x
    have hC := hComp E Ω A w h E Ω A w h rc' rc hrc'.toLit hrc
      (RingEquiv.refl Ω) (RingHom.id E) (RingEquiv.refl _) (fun _ => Iff.rfl) (fun _ => rfl) continuous_id
      (fun _ => rfl) n c.rep c.rep (LinearEquiv.refl ℂ _) (fun g v => by
        have hg : GeneralLinearGroup.map (RingEquiv.refl (w.adicCompletion E)).toRingHom g = g :=
          Units.ext (Matrix.ext fun _ _ => rfl)
        rw [hg]; rfl)
    obtain ⟨b, b', hb, hb', hN, hρ⟩ := hC
    have hbb : WD.mk b = WD.mk b' := WD.sound ⟨LinearEquiv.refl ℂ _, fun σ v => by
      simp only [LinearEquiv.refl_apply]; rw [hρ σ σ (fun _ => rfl)], fun v => by
      simp only [LinearEquiv.refl_apply]; rw [hN]⟩
    have hx : (⟨n, c⟩ : IrrGL (w.adicCompletion E)) = cls c.rep := congrArg (Sigma.mk _) c.cl_rep.symm
    rw [hx, ← hb, ← hb', hbb]
  · intro E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' rc rc' hrc hrc'
    exact hComp E Ω A w h E' Ω' A' w' h' rc rc' hrc.toLit hrc'.toLit

end GlobalTheory.LocLanglandsBridge
end

