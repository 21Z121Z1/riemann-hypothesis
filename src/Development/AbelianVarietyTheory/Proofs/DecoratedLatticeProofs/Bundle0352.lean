import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0155
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0159
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0963
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultiplicityLiftLastChainStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0144
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0360
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0163
import Formalism.LocalToGlobal.HermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitProductRescaleDisjointFinsets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Formalism.LocalToGlobal.Columns.StdLatUnimodular

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdeleEquivFin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.Th
open Formalism.L2.JoinChr Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.DetRootRead

theorem exists_adele_equiv_fin (D : D7)
    (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (hι : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x)
    (hint : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) :
    ∃ Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E, Continuous Φ ∧ Continuous Φ.symm ∧
      (∀ x : D.host.E, Φ (incA D x) = algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) x) ∧
      (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ k : D.host.Eˣ,
        Φ (locE D e (k : D.host.E)) =
          ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E)) ∧
      ∀ z : AE D, ((Φ z).1 = 1 → infPart D z = 1) ∧ (Φ z).2 = ι (finPart D z) := by
  obtain ⟨hιc, hιc'⟩ := GlobalTheory.HeckeTensorRead.continuous_finite_equiv D ι hint
  obtain ⟨j, hjc, hjc', hj⟩ := GlobalTheory.HeckeTensorRead.exists_infinite_equiv D.host.F D.host.E D.sp.cm.sig
    ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, D.sp.cm.cmUnram.2.1⟩
  obtain ⟨s, hs, hsc, hsc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  let Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E := s.trans (j.prodCongr ι)
  have hΦ : ∀ z, Φ z = (j (infPart D z), ι (finPart D z)) := fun z =>
    Prod.ext (congrArg j (hs z).1) (congrArg ι (hs z).2)
  refine ⟨Φ, (hjc.prodMap hιc).comp hsc, hsc'.comp (hjc'.prodMap hιc'), fun x => ?_, fun P e he k => ?_,
    fun z => ⟨fun h => ?_, by rw [hΦ]⟩⟩
  · rw [hΦ]
    exact Prod.ext (hj x) (hι x)
  · obtain ⟨h1, h2, h3⟩ := GlobalTheory.HeckeTensorRead.isPlIdem_parts D ι hι hint he
    rw [hΦ]
    refine Prod.ext ?_ ?_
    · have h5 : j (infPart D e) = 0 := by rw [h1]; exact j.map_zero
      exact (GlobalTheory.HeckeTensorRead.map_loc (j.toRingHom.comp (infPart D)) e _).trans (by
        change 1 + j (infPart D e) * _ = 1
        rw [h5, zero_mul, add_zero])
    · have h4 : ι (finPart D (incA D (k : D.host.E))) = algebraMap D.host.E _ (k : D.host.E) := hι k
      refine (GlobalTheory.HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _).trans ?_
      exact GlobalTheory.HeckeTensorRead.loc_eq_finSingle P _ _ _ h4 h2 h3
  · rw [hΦ] at h
    exact j.injective (h.trans j.map_one.symm)

theorem read_of_equiv (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (h : ChrEq c χ)
    (Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E) (hΦ : Continuous Φ.symm)
    (h1 : ∀ x : D.host.E, Φ (incA D x) = algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) x)
    (h2 : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ k : D.host.Eˣ,
        Φ (locE D e (k : D.host.E)) =
          ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E))
    (z : (AE D)ˣ) : ((c z : Circle) : ℂ) = ((χ.1 (Units.map Φ.toRingHom.toMonoidHom z) : ℂˣ) : ℂ) := by
  let u : Ideles D.host.E →* (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦ
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  let χ' : HChar D.host.E := ⟨Circle.toUnits.comp (MonoidHom.comp c u), ht.comp (h.1.1.comp hu), fun k => by
    have : u (diagUnits D.host.E k) = Units.map (incA D).toMonoidHom k :=
      Units.ext (Φ.symm_apply_eq.2 (h1 k).symm)
    change Circle.toUnits (c (u _)) = 1
    rw [this, h.1.2, map_one]⟩
  have h' : ChrEq c χ' := ⟨h.1, fun P e he k x hx => by
    have : x = u (localIdele D.host.E P (atFin P k)) :=
      Units.ext (Φ.eq_symm_apply.2 (by rw [hx, h2 P e he k]))
    rw [this]
    rfl⟩
  rw [GlobalTheory.ChrEqUnique.hchar_unique D c χ χ' h h']
  have : u (Units.map Φ.toRingHom.toMonoidHom z) = z := Units.ext (Φ.symm_apply_apply _)
  show ((c z : Circle) : ℂ) = ((Circle.toUnits (c (u (Units.map Φ.toRingHom.toMonoidHom z))) : ℂˣ) : ℂ)
  rw [this]
  rfl

theorem comm_sigR (D : D7) (w : Af D.host.F ⊗[D.host.F] D.host.E) :
    Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (sigR (Af D.host.F) D.sp.cm.sig w) =
      Formalism.UG.sigR D.sp.cm.sig (Af D.host.F) (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add v w hv hw => rw [RingHom.map_add, map_add, hv, hw, map_add, RingHom.map_add]

end GlobalTheory.DetRootRead

namespace GlobalTheory.DetRootRead

set_option maxHeartbeats 1000000 in

theorem chr_at_detRoot : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → χ.TrivOn D.host.F →
  ∀ (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (y : GL (Fin n) (Formalism.L2.DIV.AfE D.host.F D.host.E)), g ∈ GfC V →
    finM V hn g = (y : Matrix (Fin n) (Fin n) (Formalism.L2.DIV.AfE D.host.F D.host.E)) → ∀ x, IsDetRoot V g x → ∀ a : Neutral.B1.Ideles D.host.E,
      IsDetLift (host_cmData D.R D.host) y a → (c x : ℂ) = ((χ.1 (Chr.finPartI D.host.E a) : ℂˣ) : ℂ) := by
  intro D c χ hc ht V n hn g y hg hy x hx a ha
  let ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv.trans (afIso D.host.F D.host.E)
  have hι : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x := fun x => afIso_tmul_one _ _ x
  have hint : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1 := fun y =>
    (GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D y).trans (mem_rInt_iff _ _ _)
  obtain ⟨Φ, -, hΦ', h1, h2, h3⟩ := exists_adele_equiv_fin D ι hι hint
  let b : (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom (Chr.finPartI D.host.E a)
  have hbΦ : Φ (b : AE D) = ((Chr.finPartI D.host.E a : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E) :=
    Φ.apply_symm_apply _
  have hbinf : infPart D (b : AE D) = 1 := (h3 _).1 (by rw [hbΦ]; rfl)
  have hbfin : Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D (b : AE D)) =
      (finAf D.host.F D.host.E a : Formalism.L2.DIV.AfE D.host.F D.host.E) := by
    apply (afIso D.host.F D.host.E).injective
    rw [afIso_finAf]
    have := (h3 (b : AE D)).2
    rw [hbΦ] at this
    exact this.symm
  have hcb : ((c b : Circle) : ℂ) = ((χ.1 (Chr.finPartI D.host.E a) : ℂˣ) : ℂ) := by
    rw [read_of_equiv D c χ hc Φ hΦ' h1 h2 b]
    have hb' : Units.map Φ.toRingHom.toMonoidHom b = Chr.finPartI D.host.E a := Units.ext hbΦ
    rw [hb']
  rw [← hcb]
  obtain ⟨d, hd_def⟩ : ∃ d : AE D, d = ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det := ⟨_, rfl⟩
  have hdinf : infPart D d = 1 := by rw [hd_def]; exact GlobalTheory.DetOnto.infPart_det V g hg
  have hdfin : Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D d) =
      ((Matrix.GeneralLinearGroup.det y : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← hy]
    unfold GlobalTheory.AdForm.finM
    rw [Matrix.det_reindex_self, hd_def]
    exact (Formalism.IndefR.Datum.toEAf D).map_det (mt V g)
  have hfa : (finAf D.host.F D.host.E a : Formalism.L2.DIV.AfE D.host.F D.host.E) =
      ((Matrix.GeneralLinearGroup.det y : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E) *
        Formalism.UG.sigR D.sp.cm.sig (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (finAf D.host.F D.host.E a : Formalism.L2.DIV.AfE D.host.F D.host.E) := by
    unfold IsDetLift Formalism.L2.DIV.h90 at ha
    rw [MonoidHom.div_apply, div_eq_iff_eq_mul] at ha
    exact congrArg Units.val ha
  have hbfin' : finPart D (b : AE D) = finPart D d * sigR (Af D.host.F) D.sp.cm.sig (finPart D (b : AE D)) := by
    apply (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
    have e1 := comm_sigR D (finPart D (b : AE D))
    rw [hbfin] at e1
    refine hbfin.trans (hfa.trans ?_)
    refine Eq.trans ?_ (map_mul (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) _ _).symm
    rw [hdfin, e1]
  obtain ⟨s, hs, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have split : ∀ z w : AE D, infPart D z = infPart D w → finPart D z = finPart D w → z = w := fun z w hi hf =>
    s.injective (Prod.ext ((hs z).1.trans (hi.trans (hs w).1.symm)) ((hs z).2.trans (hf.trans (hs w).2.symm)))
  have hbd : (b : AE D) = d * sigR (AF D.host.F) D.sp.cm.sig (b : AE D) := by
    refine split _ _ ?_ ?_
    · rw [RingHom.map_mul, GlobalTheory.DetOnto.infPart_sigR, hbinf, hdinf, map_one, one_mul]
    · rw [RingHom.map_mul, GlobalTheory.DetRootChar.finPart_sigR]
      exact hbfin'
  let σU : (AE D)ˣ →* (AE D)ˣ := Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom
  have key : x * σU b = σU x * b := by
    apply Units.ext
    change (x : AE D) * sigR (AF D.host.F) D.sp.cm.sig (b : AE D) = sigR (AF D.host.F) D.sp.cm.sig (x : AE D) * (b : AE D)
    have hx' : (x : AE D) = d * sigR (AF D.host.F) D.sp.cm.sig (x : AE D) := by rw [hd_def]; exact hx
    conv_lhs => rw [hx']
    conv_rhs => rw [hbd]
    ring
  let q : (AE D)ˣ := x * b⁻¹
  have hq : σU q = q := by
    change σU (x * b⁻¹) = x * b⁻¹
    rw [map_mul, map_inv, mul_inv_eq_iff_eq_mul, mul_right_comm, eq_mul_inv_iff_mul_eq]
    exact key.symm
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
    intro x
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add, hσ, add_comm]
  obtain ⟨t, htq⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr q (congrArg Units.val hq)
  have hcq : c q = 1 := by
    rw [← htq]
    exact GlobalTheory.GridWeil.triv_base hc ht t
  have hxq : x = q * b := by simp [q]
  rw [hxq, map_mul, hcq, one_mul]

end GlobalTheory.DetRootRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarFinitePointsFourierJacobiBessel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HaarExist

theorem haar_exists : ∀ (D : D7) (V : HSp D), (∃ μ : Measure (GfC V), μ.IsHaarMeasure) ∧ ∀ (V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), (∃ μ : Measure ((jacGrp d).subgroupOf (GfC V)), μ.IsHaarMeasure) ∧ ∀ (A L : HSp D) (o : OrthDec V₀ A L), ∃ μ : Measure ((besGrp d o).subgroupOf (GfC V)), μ.IsHaarMeasure := by
  intro D V
  have hf := GlobalTheory.AdelicSplit.isClosed_GfC' V
  haveI : LocallyCompactSpace (GfC V) := hf.locallyCompactSpace
  refine ⟨⟨Measure.haar, inferInstance⟩, fun V₀ ρ d => ⟨?_, fun A L o => ?_⟩⟩
  · have hJ := GlobalTheory.jacGrp_isClosed D V V₀ ρ d
    have hc : IsClosed (((jacGrp d).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) :=
      hJ.preimage continuous_subtype_val
    haveI : LocallyCompactSpace ((jacGrp d).subgroupOf (GfC V)) := hc.locallyCompactSpace
    exact ⟨Measure.haar, inferInstance⟩
  · have hB := GlobalTheory.BesClosed.besGrp_isClosed D V V₀ A L ρ d o
    have hc : IsClosed (((besGrp d o).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) :=
      hB.preimage continuous_subtype_val
    haveI : LocallyCompactSpace ((besGrp d o).subgroupOf (GfC V)) := hc.locallyCompactSpace
    exact ⟨Measure.haar, inferInstance⟩

end GlobalTheory.HaarExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsJ
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms GlobalTheory.Core.Rk GlobalTheory.Core.Rk.Top
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.Top

theorem exists_isJ : ∀ (D : D7) (u : D.what₂.Word) (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)), ∃ j : SmT M →ₗ[ℂ] (FrP D → ℂ), (∀ (i : Fin (D.R.N D.R.m - 1)) τ, (((D.fm u).sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i) → IsJ u M j := by
  intro D u M
  by_cases hsg : ∀ (i : Fin (D.R.N D.R.m - 1)) τ, (((D.fm u).sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i
  swap
  · exact ⟨0, fun h => absurd h hsg⟩
  have hAP : GlobalTheory.DefLift.AllPlus M := GlobalTheory.DefLift.allPlus_of_le (Ptw D) (Nat.sub_le _ _) M
  have hε : ∀ τ, M.ε τ = allPos D.sp.X'.rank := fun τ => funext fun a => hAP τ a
  have hmod := fun τ => GlobalTheory.CompactModel.model_allPos D D.sp.X' _ M τ (hε τ)
  have hpar := GlobalTheory.T.neg_harishChandraParam_rev_eq_weylWeight_top D u M hsg
  have hpl : ∀ τ, ∃ (j : M.H τ →ₗ[ℂ] MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ) (d : ℕ)
      (b : Module.Basis (Fin d) ℂ (M.H τ)), (∀ ξ, j ξ ∈ delSq ℂ _ (sgT u τ)) ∧
      (∀ p ∈ delSq ℂ _ (sgT u τ), ∃ ξ, j ξ = p) ∧
      (∀ a a', normFock (sgT u τ) (j (b a)) (j (b a')) = if a = a' then 1 else 0) ∧
      ∀ g ∈ Matrix.unitaryGroup (Fin (D.R.N D.R.m - 1)) ℂ, ∀ ξ,
        j (M.σ τ (g.submatrix (Fin.cast (rankP D)) (Fin.cast (rankP D))) ξ) =
          (g.det ^ (-(sgT u τ).detShift)) • Formalism.GradedWeylDivisibility.rowAct ℂ gᴴ (j ξ) := fun τ => by
    have := (hmod τ).1
    exact GlobalTheory.T.finite_dim_unitary_K_type_eq_dual_weyl_module _ _ (rankP D) (sgT u τ) (M.H τ) (M.σ τ) (M.lam τ) (hmod τ).2.2.1 (hmod τ).2.2.2 (hpar τ)
  choose jH d bH hj1 hj2 hj3 hj4 using hpl
  obtain ⟨Jt, hJi, hJr, hJt⟩ := GlobalTheory.T.tensor_weyl_module_maps_injective_on_pure_span D.what₂.Tau (D.R.N D.R.m - 1) (sgT u) (fun τ => M.sm τ)
    (fun τ => jH τ ∘ₗ (M.sm τ).subtype) d (fun τ => (bH τ).map (LinearEquiv.ofTop (M.sm τ) (hmod τ).2.1).symm)
    (fun τ ξ => hj1 τ _) (fun τ p hp => by
      obtain ⟨ξ, hξ⟩ := hj2 τ p hp
      exact ⟨(LinearEquiv.ofTop (M.sm τ) (hmod τ).2.1).symm ξ, by simpa using hξ⟩)
    (fun τ a a' => by simpa using hj3 τ a a')

  set h := rankP D with hh
  let rd : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) ℂ → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ :=
    fun A => A.reindex (finCongr h) (finCongr h)
  let fr' : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ := fun τ => rd (M.fr τ)
  have hfr' : ∀ τ, IsUnit (fr' τ).det := fun τ => by
    simp only [fr', rd, Matrix.det_reindex_self]
    exact GlobalTheory.DefLift.fr_det M τ
  refine ⟨(fnOf (gramC (gramP D) (embT D)) (shiftOf (sgT u)) fr') ∘ₗ Jt, fun _ => ⟨?_, ?_, ?_⟩⟩
  · exact (Formalism.L2.Forms.fnOf_injective _ _ _ hfr').comp hJi
  · rw [LinearMap.range_comp, hJr]
    exact GlobalTheory.ValueSpaceCoordinates.map_fnOf_eq_ValC _ _ _ _ _ hfr'
  · intro τ g hg v w hw y y' hy
    classical
    obtain ⟨-, -, heval⟩ := GlobalTheory.FockTen.nfAll_ten D.what₂.Tau (D.R.N D.R.m - 1) (sgT u)
    simp only [LinearMap.comp_apply, hJt, heval]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    by_cases hρ : ρ = τ
    · subst hρ
      have hyτ : y.1 ρ = rd g * y'.1 ρ := by rw [hy ρ, Function.update_self]
      set mk := M.fr ρ * g * (M.fr ρ)⁻¹ with hmk
      have hwm : ((Function.update v ρ w ρ : M.sm ρ) : M.H ρ) = M.σ ρ mk (v ρ) := by
        rw [Function.update_self]; exact hw
      have hmk_u : mk ∈ Matrix.unitaryGroup (Fin D.sp.X'.rank) ℂ := by
        rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
        have hg' : gᴴ * ((M.fr ρ)ᴴ * M.fr ρ) * g = (M.fr ρ)ᴴ * M.fr ρ := by rw [← hAP.gram]; exact hg
        have e1 : M.fr ρ * (M.fr ρ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (GlobalTheory.DefLift.fr_det M ρ)
        calc mkᴴ * mk = ((M.fr ρ)⁻¹)ᴴ * (gᴴ * ((M.fr ρ)ᴴ * M.fr ρ) * g) * (M.fr ρ)⁻¹ := by
              simp only [hmk, Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = (M.fr ρ * (M.fr ρ)⁻¹)ᴴ * (M.fr ρ * (M.fr ρ)⁻¹) := by
              rw [hg']; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = 1 := by rw [e1, Matrix.conjTranspose_one, Matrix.one_mul]
      have hrdmul : ∀ A B, rd (A * B) = rd A * rd B := fun A B => by
        simp only [rd, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
      have hgn_u : rd mk ∈ Matrix.unitaryGroup _ ℂ := by
        rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hmk_u ⊢
        have : (rd mk)ᴴ = rd mkᴴ := by simp only [rd, Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
        rw [this, ← hrdmul, hmk_u]
        simp only [rd, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
      have hsub : (rd mk).submatrix (Fin.cast h) (Fin.cast h) = mk := by
        ext i j; simp [rd, Matrix.reindex_apply]
      have hrd : rd mk = fr' ρ * rd g * (fr' ρ)⁻¹ := by
        simp only [hmk, hrdmul, fr']
        congr 1
        simp only [rd, Matrix.inv_reindex]
      have key := hj4 ρ (rd mk) hgn_u (v ρ)
      rw [hsub] at key
      simp only [Submodule.coe_subtype]
      rw [hwm, key]
      have hoU : IsUnit ((fr' ρ)⁻¹).det := by
        rw [Matrix.det_nonsing_inv]; exact (hfr' ρ).ringInverse
      have hab : y.1 ρ = (fr' ρ)⁻¹ * rd mk * ((fr' ρ)⁻¹)⁻¹ * y'.1 ρ := by
        rw [Matrix.nonsing_inv_nonsing_inv _ (hfr' ρ), hrd, hyτ]
        simp only [Matrix.mul_assoc]
        rw [Matrix.nonsing_inv_mul_cancel_left _ _ (hfr' ρ), Matrix.nonsing_inv_mul_cancel_left _ _ (hfr' ρ)]
      have hfe := GlobalTheory.TenTypes.factor_eq (rd mk) (fr' ρ)⁻¹ (y.1 ρ) (y'.1 ρ) hgn_u hoU (shiftOf (sgT u) ρ) (jH ρ (v ρ)) hab
      rw [Matrix.nonsing_inv_nonsing_inv _ (hfr' ρ)] at hfe
      exact hfe
    · have hyρ : y.1 ρ = y'.1 ρ := by rw [hy ρ, Function.update_of_ne hρ, Matrix.one_mul]
      rw [hyρ]
      simp only [Submodule.coe_subtype, Function.update_of_ne hρ]

end GlobalTheory.Core.Rk.Top
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLevelElementsStepVector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockVecSum

theorem fockVec_eq_sum : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ t j, j + 1 < D.R.m → ∀ [Fintype (lvP W).H], ∃ κ : (lvP W).H → GA D (Yc D j), (∀ p, κ p ∈ levS (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W))) ∧ ∀ v, IsStepVecOf (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) ((pk W).ΛY j) ((pk W).ΛY (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1)) ((pk W).datYt t j (lvP W)) ((pk W).chi (j + 1)) ((pk W).Q t) ((pk W).xiR t) ((pk W).vac j) v → ∀ Q, pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) v Q = ∑ p, (levChi (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) (κ p))⁻¹ • ((pk W).ωY t j (κ p, 1)) ((pk W).ptY t j Q) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW t j hj _
  have hC := hW.bot.hyp.2.2.2.1
  have hL : (pk W).toLevCh.Is W.P.A3.A.μ0 := hC.lev
  have hj' : j < D.R.m := Nat.lt_of_succ_lt hj
  have hlift := GlobalTheory.ChainEquiv.lifts_chain (pk W).toLevCh W.P.A3.A.μ0 hL t j hj'
  choose κ hκ using fun p : (lvP W).H => hlift p.1
  refine ⟨κ, fun p => ⟨(hκ p).1, (hκ p).2.1, (hκ p).2.2 ▸ p.2⟩, fun v hv Q => ?_⟩
  obtain ⟨⟨a1, a2, a3⟩, b1, b2, b3⟩ := GlobalTheory.StepVecLaw.levRes_chrStep hL t ⟨j, hj'⟩
  obtain ⟨c, hc⟩ := hL.βY j hj'
  obtain ⟨c', hc'⟩ := hL.βY (j + 1) hj
  have hω := hC.chain.ωY t j hj
  have hvY := hC.chain.vY t j hj
  have hsum := GlobalTheory.StepVecSum.stepVec_eq_sum D (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) _ _ ((pk W).ωY t j) _ _
    ((pk W).ΛY j) ((pk W).ΛY (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1)) ((pk W).vac j) ((pk W).vY t j) v hω
    (D.sp.Y_sig _) (D.sp.Y_sig _) (GlobalTheory.Chain.VacVec.cart_isCartanInv ((pk W).MY j))
    (GlobalTheory.Chain.VacVec.cart_isCartanInv ((pk W).MY (j + 1)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY j hj'))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY (j + 1) hj)) hc.1 hc'.1 D.R.r D.R.t j (r_le_Y j)
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj'.le]; rfl)
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj.le]; rfl)
    (pk W).Pg ((pk W).Q t) (GlobalTheory.T.levelCharacters_unramified_off_levelPlaces D _ _ _ hL t).1 (pk W).chi ((pk W).xiR t) (lvP W) hvY hv
    (fun PP hP => ⟨a1 PP hP, b1 PP hP⟩) (fun PP hP => ⟨a2 PP hP, b2 PP hP⟩) a3 b3 κ hκ
  have hθ : IsInfFam (pk W).θ := hvY.1.2.inf
  have hf : IsThetaFunO (pk W).ψ (Yc D j) (Yc D (j + 1)) ((pk W).vY t j) := by
    have := hC.chain.ptY t j hj 1
    rwa [RealDat.ptY, GlobalTheory.FiniteFock.pureTensorO_one] at this
  rw [hsum, GlobalTheory.SpecFac.pureTensorO_sum hω.std hθ _ _ _ _ Finset.univ _ _ (fun p _ => hω.om_pres _ _ hf)]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  have hk := GlobalTheory.FiniteFock.compAt_mt_of_finite (pk W).θ
  refine ((GlobalTheory.OrientedHeis.om_pureTensorO D _ _ _ _ _ _ _ hω hθ _ _ _ _ _ _ _ _ (κ p) 1
    (fun τ => by rw [hk τ (hκ p).1, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [hk τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [hk τ (hκ p).1, Matrix.one_mul])
    (fun τ => by rw [hk τ (one_mem _), Matrix.one_mul]) _ hf Q).2).symm

end GlobalTheory.FockVecSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemStdHom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.AdForm

variable {D : D7}

theorem coe_colStdLat (n : ℕ) :
    ((Formalism.L2.Col.stdLat D.host.E n : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = intVec D n := by
  ext x
  simp only [SetLike.mem_coe, Formalism.L2.Col.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  exact forall_congr' fun k => ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun hy => ⟨⟨_, hy⟩, rfl⟩⟩

theorem exists_nsmul_mem_stdHom (S T : HSp D) : ∃ K : ℕ, 0 < K ∧ ∀ t : WO S T, t.map (infPart D) = 0 →
    (∀ i j, toEAf D (t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → K • t ∈ stdHom S T := by
  obtain ⟨K, hK, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T)
    (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := S.rank)) (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := T.rank))
  refine ⟨K, hK, fun t ht hi => ?_⟩
  have := h t ht hi
  rwa [coe_colStdLat, coe_colStdLat] at this

theorem infPart_liftFin (x : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (GlobalTheory.LatticeStable.liftFin D x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, RingHom.map_zero]
  | tmul a m => exact GlobalTheory.LatVac.infPart_pair a m
  | add x y hx hy => rw [LinearMap.map_add, RingHom.map_add, hx, hy, add_zero]

theorem finPart_liftFin (x : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (GlobalTheory.LatticeStable.liftFin D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, RingHom.map_zero]
  | tmul a m => rfl
  | add x y hx hy => rw [LinearMap.map_add, RingHom.map_add, hx, hy]

theorem toEAf_eq_comm (z : AE D) :
    toEAf D z = Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D z) := rfl

theorem toEAf_liftFin (r : EAf D) :
    toEAf D (GlobalTheory.LatticeStable.liftFin D ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm r)) = r := by
  rw [toEAf_eq_comm, finPart_liftFin, AlgEquiv.apply_symm_apply]

theorem toEAf_approx_eq_zero (t L : AE D) (x : D.host.E) (M : ℕ) (r : EAf D)
    (ht : toEAf D t = eToEAf D x + (M : EAf D) * r) (hL : toEAf D L = -r) :
    toEAf D (incA D x - t - (M : AE D) * L) = 0 := by
  have hi : toEAf D (incA D x) = eToEAf D x := rfl
  rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, map_natCast, hi, ht, hL]
  ring

theorem approx_entry (t : AE D) (M : ℕ) (hM : 0 < M) : ∃ (x : D.host.E) (w : AE D), infPart D w = 0 ∧
    toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ finPart D (incA D x - t - (M : AE D) * w) = 0 := by
  have hM0 : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  obtain ⟨x, r, hr, e⟩ := GlobalTheory.AdeleBaseChange.exists_approx (F := D.host.F) (E := D.host.E)
    (eToEAf D (M : D.host.E)⁻¹ * toEAf D t)
  let c := Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E
  refine ⟨M * x, GlobalTheory.LatticeStable.liftFin D (c.symm (-r)), infPart_liftFin _, ?_, ?_⟩
  · rw [toEAf_liftFin]
    exact neg_mem hr
  · have ht : toEAf D t = eToEAf D (M * x) + (M : EAf D) * r := by
      have e2 := congrArg (eToEAf D (M : D.host.E) * ·) e
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul] at e2
      rw [e2, map_mul, map_natCast, mul_add]
      rfl
    have hz := toEAf_approx_eq_zero t _ (M * x) M r ht (toEAf_liftFin (-r))
    rw [toEAf_eq_comm] at hz
    exact c.injective (hz.trans (map_zero c).symm)

theorem exists_rat_half_approx : ∀ {D : D7} (S T : HSp D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → ∀ (N : ℕ), 0 < N → ∀ y : WO S T, ∃ (γ₀ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (v : WO S T), v ∈ stdHom S T ∧ IsHalf e v ∧ γ₀.map (fun r => e * incA D r) = e • y + N • v := by
  intro D S T e P he N hN y
  obtain ⟨K, hK, hKm⟩ := exists_nsmul_mem_stdHom S T
  choose x w hw0 hwi hz using fun i j => approx_entry (y i j) (N * K) (Nat.mul_pos hN hK)
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hKw : K • (Matrix.of fun i j => w i j) ∈ stdHom S T := hKm _ (Matrix.ext fun i j => hw0 i j) hwi
  refine ⟨Matrix.of x, e • (K • Matrix.of fun i j => w i j), ?_, ?_, ?_⟩
  · exact GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hee])) _ hKw
  · intro i j
    change e * (e * _) = e * _
    rw [← mul_assoc, hee]
  · ext i j
    have h0 : e * (incA D (x i j) - y i j - ((N * K : ℕ) : AE D) * w i j) = 0 := by
      refine GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_
      · rw [map_mul, hinf, zero_mul]
      · rw [map_mul, hz i j, mul_zero]
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
    push_cast at h0
    linear_combination h0

end GlobalTheory.AdForm
end
end

