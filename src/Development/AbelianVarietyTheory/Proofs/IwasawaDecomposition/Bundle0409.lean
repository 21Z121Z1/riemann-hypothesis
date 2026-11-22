import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0939
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0399
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0348
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0403
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.Bundle0035
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIrreducibleBaseChangeWeightTensorDualRepOfEmbe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotypicHeckeOperatorHyperspecialActsByScalar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfFinite
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtIn

theorem exists_int_of_finite {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {G : Type} [Group G] [Finite G]
    (f : G →* ℂˣ) (g : G) (h : ∃ y : K, σ y = ((f g : ℂˣ) : ℂ)) : ∃ z : 𝓞 K, σ (z : K) = ((f g : ℂˣ) : ℂ) := by
  obtain ⟨y, hy⟩ := h
  have hn : 0 < Nat.card G := Nat.card_pos
  have hfg : (f g) ^ Nat.card G = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
  have hy1 : y ^ Nat.card G = 1 := by
    apply σ.injective
    rw [map_pow, hy, map_one, ← Units.val_pow_eq_pow_val, hfg, Units.val_one]
  have hint : IsIntegral ℤ y := IsIntegral.of_pow hn (by rw [hy1]; exact isIntegral_one)
  exact ⟨⟨y, hint⟩, hy⟩

end GlobalTheory.MtIn

open GlobalTheory.MtIn in

theorem GlobalTheory.MtIn.levChi_integral : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L → ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (k : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J), ∃ z : 𝓞 X.toD7.what₂.LL, X.toD7.what₂.embLL (z : X.toD7.what₂.LL) = ((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ k : ℂ) := by
  intro X px I U L hI hL i t k
  have hfin : ∀ PP : Pl X.toD7.host.E, Finite (kP PP)ˣ := fun PP =>
    haveI : Finite (kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
    Finite.of_injective _ Units.val_injective
  have lift : ∀ (PP : Pl X.toD7.host.E) (d : (kP PP)ˣ), ∃ (a : 𝓞 X.toD7.host.E) (kE : X.toD7.host.Eˣ),
      (kE : X.toD7.host.E) = a ∧ (d : kP PP) = Ideal.Quotient.mk _ a := by
    intro PP d
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (d : kP PP)
    have ha0 : (a : X.toD7.host.E) ≠ 0 := by
      intro h0
      have : a = 0 := by exact_mod_cast h0
      apply d.ne_zero
      rw [← ha, this, map_zero]
    exact ⟨a, Units.mk0 _ ha0, rfl, ha.symm⟩
  have hchi : ∀ PP ∈ L.Pg, ∀ d : (kP PP)ˣ, ∃ y, X.toD7.what₂.embLL y = (((L.chi ((i : ℕ) + 1) PP)⁻¹ d : ℂˣ) : ℂ) := by
    intro PP hPP d
    obtain ⟨a, kE, h1, h2⟩ := lift PP d
    have hres := hL.is.chi i PP hPP a kE d h1 h2
    rw [hres, hL.C]
    have hw : PP ∈ (X.B.primes px).vGs := hL.Pg ▸ hPP
    exact ⟨_, ((hI.ch_tied.mu0 i).atg ⟨PP, hw⟩ kE a d h1 h2).symm⟩
  have hxi : ∀ PP ∈ L.Q t, ∀ d : (kP PP)ˣ, ∃ y, X.toD7.what₂.embLL y = ((L.xiR t PP d : ℂˣ) : ℂ) := by
    intro PP hPP d
    obtain ⟨a, kE, h1, h2⟩ := lift PP d
    have hres := hL.is.xiR t PP hPP a kE d h1 h2
    rw [hres, hL.xiH t]
    exact ⟨_, (hI.xi_reads (ixOf I U t) _).symm⟩
  let Pr : ℂˣ → Prop := fun u => ∃ z : 𝓞 X.toD7.what₂.LL, X.toD7.what₂.embLL (z : X.toD7.what₂.LL) = (u : ℂ)
  have hmul : ∀ a b : ℂˣ, Pr a → Pr b → Pr (a * b) := by
    rintro a b ⟨za, ha⟩ ⟨zb, hb⟩
    exact ⟨za * zb, by rw [Units.val_mul, ← ha, ← hb, ← map_mul]; rfl⟩
  have hone : Pr 1 := ⟨1, by rw [Units.val_one, ← map_one X.toD7.what₂.embLL]; rfl⟩
  have gchi : ∀ PP ∈ L.Pg, ∀ (c : ℕ) (d : (kP PP)ˣ), Pr ((if Frm.A = Frm.B then (fun _ : ℕ => L.chi ((i : ℕ) + 1)) else
      fun (_ : ℕ) (PP : Pl X.toD7.host.E) => (L.chi ((i : ℕ) + 1) PP)⁻¹) c PP d) := by
    intro PP hPP c d
    haveI := hfin PP
    have e : (if Frm.A = Frm.B then (fun _ : ℕ => L.chi ((i : ℕ) + 1)) else fun (_ : ℕ) (PP : Pl X.toD7.host.E) => (L.chi ((i : ℕ) + 1) PP)⁻¹) =
        fun (_ : ℕ) (PP : Pl X.toD7.host.E) => (L.chi ((i : ℕ) + 1) PP)⁻¹ := if_neg (by decide)
    rw [e]
    exact exists_int_of_finite X.toD7.what₂.embLL (L.chi ((i : ℕ) + 1) PP)⁻¹ d (hchi PP hPP d)
  have gxi : ∀ PP ∈ L.Q t, ∀ d : (kP PP)ˣ, Pr ((if Frm.A = Frm.B then (fun PP => (L.xiR t PP)⁻¹) else L.xiR t) PP d) := by
    intro PP hPP d
    haveI := hfin PP
    have e : (if Frm.A = Frm.B then (fun PP => (L.xiR t PP)⁻¹) else L.xiR t) = L.xiR t := if_neg (by decide)
    rw [e]
    exact exists_int_of_finite X.toD7.what₂.embLL (L.xiR t PP) d (hxi PP hPP d)
  show Pr (Formalism.L2.DIV.levFn (L.βV i) (flag1L (L.datVt i t)) _)
  unfold Formalism.L2.DIV.levFn
  refine hmul _ _ (hmul _ _ ?_ (Finset.prod_induction _ Pr hmul hone fun PP hPP =>
    Finset.prod_induction _ Pr hmul hone fun c _ => ?_)) (Finset.prod_induction _ Pr hmul hone fun PP hPP => ?_)
  · unfold Formalism.L2.DIV.ext1
    split_ifs
    · exact hone
    · exact hone
  · exact gchi PP hPP (c + 1) _
  · exact gxi PP hPP _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitFrame
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn

theorem isOrthF_one {D : D7} (V : HSp D) (h : V.gram = 1) : GlobalTheory.StdFrameExist.IsOrthF V 1 := by
  unfold GlobalTheory.StdFrameExist.IsOrthF GlobalTheory.StdFrameExist.gA
  rw [h, Matrix.map_one _ (map_zero _) (map_one _), Units.val_one, Formalism.UG.cT_one, Matrix.mul_one, Matrix.mul_one]

theorem intM_one {D : D7} (n : ℕ) : GlobalTheory.StdFrameExist.IntM (GlobalTheory.StdFrameExist.SI D) (1 : GL (Fin n) (Lev.EAf D)).1 := by
  intro i j
  rw [Units.val_one, Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem exists_unit_frame : ∀ (D : D7) (V : HSp D) (hF : D.host.F = maximalRealSubfield D.host.E), V.gram = 1 → Seed.FrmC.StdLat V → ∃ P : principalLevelFrame.RowPsi V V.rank, StdFrame hF P ∧ UnitFr P := by
  intro D V hF hg hV
  have h := isOrthF_one V hg
  refine ⟨GlobalTheory.StdFrameExist.rowPsi V 1 h, GlobalTheory.StdFrameExist.stdFrame_rowPsi hF hV h (intM_one _) ?_, fun κ => ?_⟩
  · rw [inv_one]; exact intM_one _
  · show finE V (GlobalTheory.StdFrameExist.psiF V 1 h κ) = _
    rw [GlobalTheory.StdFrameExist.finE_psiF, one_mul, inv_one, mul_one]
    rfl

end GlobalTheory.MtIn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteTypeIsotypicPartEqISupEquivariantHomsFrame
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

namespace GlobalTheory.IsotHom

theorem isotIn_eq_iSup_homInto : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) {n : ℕ} (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n), principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) π = ⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (finRep M) (allMaps θ M), LinearMap.range f := by
  intro D V S θ M n P π
  classical
  set e := GlobalTheory.KapIsot.eqv P with he
  have hσ : ∀ κ (x : π.S), ((GlobalTheory.OccRowVec.finRep π).comp e.symm.toMonoidHom) (e κ) x = GlobalTheory.OccRowVec.finRep π κ x := fun κ x => by
    show GlobalTheory.OccRowVec.finRep π (e.symm (e κ)) x = _
    rw [MulEquiv.symm_apply_apply]
  have hact : ∀ κ (T : MMap M), principalLevelFrame.actM P M κ T = finRep M (e κ) T := fun κ T => by
    refine MultilinearMap.ext fun v => funext fun g => ?_
    rw [principalLevelFrame.actM_apply, finRep_apply]
    rfl
  have hle : principalLevelFrame.Minf θ P M ≤ allMaps θ M := iSup_le fun N => GlobalTheory.PartDims.mult_le θ M fun k hk => hk.elim
  apply le_antisymm
  · refine iSup₂_le fun Φ hΦ => ?_
    refine le_iSup₂_of_le (f := fun f (_ : f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp e.symm.toMonoidHom) (finRep M) (allMaps θ M)) => LinearMap.range f) Φ ⟨fun s => hle (hΦ.2 ⟨s, rfl⟩), fun g s => ?_⟩ le_rfl
    obtain ⟨κ, rfl⟩ := e.surjective g
    rw [hσ, ← hact]
    exact hΦ.1 κ s
  · refine iSup₂_le fun f hf => ?_
    have hfe : principalLevelFrame.IsEqvA (principalLevelFrame.actM P M) π f := by
      intro κ x
      have h1 := hf.2 (e κ) x
      rw [hσ, ← hact] at h1
      exact h1
    have hfr : LinearMap.range f ≤ principalLevelFrame.Minf θ P M := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨N, hN, hfix⟩ := π.smooth x x.2
      obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      refine Submodule.mem_iSup_of_mem N (Submodule.subset_span ?_)
      have h1 := (GlobalTheory.MultMem.mem_mult_iff ..).1 (hf.1 x)
      refine ⟨h1.aut, h1.cusp, ?_, h1.equiv, h1.cont⟩
      rintro v _ ⟨κ, hκ, rfl⟩ g
      have h2 := hfe κ x
      rw [show (⟨Formalism.L2.NG.rt D.host.E n κ x, π.stable κ x x.2⟩ : π.S) = x from Subtype.ext (hfix κ hκ)] at h2
      rw [one_mul]
      exact (congrArg (fun T : MMap M => T v g) h2).symm
    exact le_iSup₂_of_le (f := fun (Φ : π.S →ₗ[ℂ] MMap M) (_ : principalLevelFrame.IsEqvA (principalLevelFrame.actM P M) π Φ ∧ LinearMap.range Φ ≤ principalLevelFrame.Minf θ P M) => LinearMap.range Φ) f ⟨hfe, hfr⟩ le_rfl

end GlobalTheory.IsotHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedSpaceLeSupEigenspacesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_space_le_sup_eigenspaces : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host), HkCond D T i j k P →
      V0T D T S In.rho In.chi In.θ i j b ≤
        ⨆ σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ},
          Module.End.eigenspace (hkT D T S In i j b k P)
            (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)) := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.V0T_le_iSup_eigenspace | exact GlobalTheory.HeightCounting.FormsStep.V0T_le_iSup_eigenspace | (intros; apply GlobalTheory.HeightCounting.FormsStep.V0T_le_iSup_eigenspace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.HeckeEigConj

theorem proj_conjSplit {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (z : AL L) :
    (GlobalTheory.HeckeFrob.conjSplit s).proj z = s.proj (conjAL L z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | tmul a b =>
    simp only [SplitPlace.proj, conjAL, GlobalTheory.HeckeFrob.conjSplit, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]; rfl

theorem map_loc_conjSplit (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) {K' : Type}
    [Field K'] (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* K') (x : GAf L n) :
    Matrix.GeneralLinearGroup.map i.toRingHom ((GlobalTheory.HeckeFrob.conjSplit s).loc n x) =
      GlobalTheory.LFun.ConjPlace.invT i n (s.loc n x) := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [GlobalTheory.LFun.ConjPlace.invT_val, ← map_inv]
  have h := congrFun₂ (GlobalTheory.FinTypCount.inv_val x) b a
  change i ((GlobalTheory.HeckeFrob.conjSplit s).proj _) = i (s.proj ((((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix _ _ _) b a))
  rw [h, proj_conjSplit]
  rfl

theorem KO_eq_KGL (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) = GlobalTheory.LFun.KGL w n := by
  ext g
  rw [GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.HeckeScalarSph.mem_GLint_iff]
  have h : ∀ x : w.adicCompletion E, x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ Formalism.UG.Ov E w := fun x =>
    (Valuation.mem_integer_iff _ _).trans (GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff w x)
  simp only [h]

theorem heckeD_eq_sum_of_agree {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (GAf L n)) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))}
    (hJ : ∀ κ, TrivOutside {v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) {D : Set (GAf L n)} (hD : ∀ x ∈ D, TrivOutside {v} x)
    {R : Finset (GAf L n)} (h1 : ∀ γ ∈ R, γ ∈ D) (h2 : ∀ x ∈ D, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n)
    {f : GAf L n → W} (hf : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) :
    NG.heckeD J D f = ∑ γ ∈ R, NG.rt L n γ f := by
  classical
  have hmem : ∀ x ∈ D, ∀ y ∈ D, (x⁻¹ * y ∈ J ↔ x⁻¹ * y ∈ Umax L n) := fun x hx y hy =>
    hJ _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hD x hx)) (hD y hy))
  funext g
  rw [Finset.sum_apply, NG.heckeD, finsum_eq_sum_of_support_subset (s := R.image fun x : GAf L n => (x : GAf L n ⧸ J)),
    Finset.sum_image]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    have hc : ∃ x ∈ D, (x : GAf L n ⧸ J) = γ := ⟨γ, h1 γ hγ, rfl⟩
    rw [dif_pos hc]
    have hu : γ⁻¹ * hc.choose ∈ Umax L n :=
      (hmem γ (h1 γ hγ) _ hc.choose_spec.1).1 (QuotientGroup.eq.1 hc.choose_spec.2.symm)
    have := congrFun (hf _ hu (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hD γ (h1 γ hγ)))
      (hD _ hc.choose_spec.1))) (g * γ)
    refine Eq.trans ?_ this
    show f _ = f _
    congr 1
    group
  · intro γ hγ δ hδ e
    exact (h2 δ (h1 δ hδ)).unique ⟨hγ, (hmem γ (h1 γ hγ) δ (h1 δ hδ)).1 (QuotientGroup.eq.1 e)⟩
      ⟨hδ, by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro c hc
    by_cases h : ∃ x ∈ D, (x : GAf L n ⧸ J) = c
    · obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨γ, ⟨hγ, e⟩, -⟩ := h2 x hx
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, hγ, QuotientGroup.eq.2 ((hmem γ (h1 γ hγ) x hx).2 e)⟩)
    · exact absurd (dif_neg h) hc

theorem norms_eq {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    Formalism.UG.qV L (GlobalTheory.HeckeFrob.conjSplit s).w = normV (GlobalTheory.HeckeFrob.conjSplit s).w ∧
      s.q = normV (GlobalTheory.HeckeFrob.conjSplit s).w := by
  refine ⟨?_, ?_⟩
  · rw [Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply, normV]
  · rw [normV, (GlobalTheory.HeckeFrob.conjSplit s).card_quot]
    rfl

end GlobalTheory.HeckeEigConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeElementUniformizerRatioDeterminant
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.EtaDet

open Formalism.L2.Col in

theorem prod_diag_inv {E : Type} [Field E] [NumberField E] [StarRing E] (n : ℕ) (π : 𝓞 E) (d : ℕ) (hd : d ≤ n) :
    ∏ i : Fin n, (mhlDiag n π d i)⁻¹ = (mhlA π)⁻¹ ^ d := by
  have h1 : ∀ i : Fin n, (mhlDiag n π d i)⁻¹ = (fun j : ℕ => if j < d then (mhlA π)⁻¹ else 1) i.1 := by
    intro i
    unfold mhlDiag
    by_cases h : i.1 < d <;> simp [h]
  rw [Finset.prod_congr rfl fun i _ => h1 i, Fin.prod_univ_eq_prod_range (fun j : ℕ => if j < d then (mhlA π)⁻¹ else 1) n,
    Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  have : (Finset.range n).filter (fun j => j < d) = Finset.range d := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.card_range]

theorem idem_mul_pow {R : Type} [CommRing R] {e : R} (hee : e * e = e) (x : R) (d : ℕ) : e * (e * x) ^ d = e * x ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, pow_succ, ← mul_assoc, ih]
    rw [show e * x ^ d * (e * x) = (e * e) * (x ^ d * x) by ring, hee]

theorem pow_mem_int {D : D7} {x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (d : ℕ) :
    x ^ d ∈ intAE D := by
  induction d with
  | zero => rw [pow_zero]; exact GlobalTheory.HeckeConj.one_mem_intAE D
  | succ d ih => rw [pow_succ]; exact GlobalTheory.HeckeConj.mul_mem_intAE D ih hx

theorem unit_mem {D : D7} {e a : Formalism.L2.Theta.AE D} (hee : e * e = e) (ha : finPart D (e * a) ∈ intAE D) (d : ℕ) :
    finPart D (e * a ^ d + (1 - e)) ∈ intAE D := by
  have he : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])
  rw [← idem_mul_pow hee a d, RingHom.map_add, RingHom.map_sub, RingHom.map_one, RingHom.map_mul, RingHom.map_pow]
  exact add_mem (GlobalTheory.HeckeConj.mul_mem_intAE D he (pow_mem_int ha d)) (sub_mem (GlobalTheory.HeckeConj.one_mem_intAE D) he)

theorem det_castGL {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (g : GL (Fin m) R) :
    Matrix.GeneralLinearGroup.det (castGL h g) = Matrix.GeneralLinearGroup.det g := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, castGL, Matrix.det_reindex_self]

theorem det_fin {D : D7} (V : HSp D) (α : GA D V) : finPart D (Formalism.L2.Theta.mt V α).det = (finHom V α).val.det := by
  rw [RingHom.map_det]; rfl

theorem det_swap {D : D7} {m : ℕ} (g : GL (Fin m) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) :
    swapAE D g.val.det = (Formalism.UG.bc (swapAE D) g).val.det := by
  rw [RingHom.map_det]; rfl

theorem det_cast {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (g : GL (Fin m) R) : (castGL h g).val.det = g.val.det := by
  have := congrArg Units.val (det_castGL h g)
  simpa only [Matrix.GeneralLinearGroup.val_det_apply] using this

theorem det_conj_inv {R : Type} [CommRing R] {n : ℕ} (C η : GL (Fin n) R) : ((C * η * C⁻¹)⁻¹).val.det = (η⁻¹).val.det := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.GeneralLinearGroup.val_det_apply]
  congr 1
  rw [map_inv, map_inv, map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]

theorem cast_inv {D : D7} (V : HSp D) {n : ℕ} (h : n = V.rank) (α : GA D V) :
    castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α⁻¹)) = (castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)))⁻¹ := by
  rw [map_inv (finHom V) α, map_inv (Formalism.UG.bc (swapAE D)), map_inv (castGL h.symm)]

end GlobalTheory.Mem.R3.LiftBrg.EtaDet

namespace GlobalTheory.Mem.R3.LiftBrg.EtaDet

theorem det_transport {D : D7} (V : HSp D) {n : ℕ} (h : n = V.rank) (α : GA D V) (C η : GL (Fin n) (Formalism.IndefR.Lev.EAf D))
    (hC : castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * η * C⁻¹) :
    swapAE D (finPart D (Formalism.L2.Theta.mt V α⁻¹).det) = (η⁻¹).val.det := by
  have hg : castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α⁻¹)) = (C * η * C⁻¹)⁻¹ := by
    rw [cast_inv V h α, hC]
  rw [det_fin V α⁻¹, det_swap (finHom V α⁻¹), ← det_cast h.symm (Formalism.UG.bc (swapAE D) (finHom V α⁻¹)), hg,
    det_conj_inv C η]

theorem prV_det_eta {D : D7} (n : ℕ) [NeZero n] (v : HeightOneSpectrum (𝓞 D.host.F)) {π : 𝓞 D.host.E} (hπ0 : π ≠ 0)
    (d : ℕ) :
    Formalism.UG.prV v ((((Formalism.L2.Col.mhlEta D.sp.cm n v hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) :
      GL (Fin n) (Formalism.IndefR.Lev.EAf D))⁻¹).val.det -
        Formalism.L2.Col.iA D.host.F D.host.E (∏ k : Fin n, (Formalism.L2.Col.mhlDiag n π d k)⁻¹)) = 0 := by
  have hdiag : ∀ i j : Fin n, Formalism.UG.prV v ((((Formalism.L2.Col.mhlEta D.sp.cm n v hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) :
      GL (Fin n) (Formalism.IndefR.Lev.EAf D))⁻¹).val i j) =
      Formalism.UG.prV v ((Matrix.diagonal fun k => Formalism.L2.Col.iA D.host.F D.host.E (Formalism.L2.Col.mhlDiag n π d k)⁻¹) i j) := by
    intro i j
    rw [Formalism.L2.Col.mhl_prV_eta_inv, Matrix.diagonal_apply]
    by_cases hij : i = j <;> simp [hij]
  have hm : (Formalism.UG.prV v).mapMatrix (((Formalism.L2.Col.mhlEta D.sp.cm n v hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) :
      GL (Fin n) (Formalism.IndefR.Lev.EAf D))⁻¹).val =
      (Formalism.UG.prV v).mapMatrix (Matrix.diagonal fun k => Formalism.L2.Col.iA D.host.F D.host.E (Formalism.L2.Col.mhlDiag n π d k)⁻¹) :=
    Matrix.ext hdiag
  rw [RingHom.map_sub, RingHom.map_det, hm, ← RingHom.map_det, Matrix.det_diagonal,
    map_prod (Formalism.L2.Col.iA D.host.F D.host.E), sub_self]

end GlobalTheory.Mem.R3.LiftBrg.EtaDet

namespace GlobalTheory.Mem.R3.LiftBrg.EtaDet

theorem hom_mul_pow {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a b : R) (d : ℕ) :
    f ((a * b) ^ d) = f a ^ d * f b ^ d := by
  rw [map_pow, map_mul, mul_pow]

theorem final_alg {R : Type} [CommRing R] {e Δ c X W : R} (hee : e * e = e) (key : e * Δ = e * c) (hc : c = X * W) :
    e * Δ = e * W * (e * X + (1 - e)) := by
  linear_combination key + e * hc + (W - W * X) * hee

theorem swap_inj {D : D7} {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (h : swapAE D x = swapAE D y) :
    x = y :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective h

theorem idem_eq_of_swap {D : D7} {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {x c : Formalism.L2.Theta.AE D}
    (h : swapAE D (finPart D e) * swapAE D (finPart D x) = swapAE D (finPart D e) * swapAE D (finPart D c)) :
    e * x = e * c := by
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · simp only [RingHom.map_mul, GlobalTheory.SplitScalar.infPart_splitIdem he, zero_mul]
  · apply swap_inj
    rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul]
    exact h

end GlobalTheory.Mem.R3.LiftBrg.EtaDet

namespace GlobalTheory.Mem.R3.LiftBrg.EtaDet

theorem det_clause : ∀ {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (e : Formalism.L2.Theta.AE D) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V), d ≤ n → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → (∀ z : Formalism.IndefR.Lev.EAf D, Formalism.UG.prV v z = 0 → swapAE D (finPart D e) * z = 0) → α ∈ GfC V → castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹ →
    ∃ u u' : Formalism.L2.Theta.AE D, finPart D u ∈ intAE D ∧ finPart D u' ∈ intAE D ∧ e * u * u' = e ∧
      e * (mt V α⁻¹).det = e * incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E) ^ d * u := by
  intro D V n _ h v Pb Ut d e C α hd he hε hα hC
  have hπ0 : ((Ut.π : 𝓞 D.host.E) : D.host.E) ≠ 0 := Formalism.L2.Col.mhl_alg_ne Ut.hπ0
  have hee : e * e = e := he.1.1
  have hfe : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])
  have hinv : finPart D (e * incA D ((Ut.π : D.host.E))⁻¹) ∈ intAE D := by
    by_contra hc
    exact Ut.hπP ((he.2 Ut.π Ut.hπ0).2 hc)
  have hpi : finPart D (e * incA D (Ut.π : D.host.E)) ∈ intAE D := by
    rw [RingHom.map_mul]
    exact GlobalTheory.HeckeConj.mul_mem_intAE D hfe (AddSubgroup.subset_closure ⟨1, fun v => one_mem _, Ut.π, rfl⟩)
  have hXY : incA D ((Ut.π : D.host.E))⁻¹ ^ d * incA D (Ut.π : D.host.E) ^ d = 1 := by
    rw [← mul_pow, ← RingHom.map_mul, inv_mul_cancel₀ hπ0, RingHom.map_one, one_pow]
  refine ⟨e * incA D ((Ut.π : D.host.E))⁻¹ ^ d + (1 - e), e * incA D (Ut.π : D.host.E) ^ d + (1 - e),
    unit_mem hee hinv d, unit_mem hee hpi d, ?_, ?_⟩
  · linear_combination e * hXY + ((e + 1) * (incA D ((Ut.π : D.host.E))⁻¹ ^ d * incA D (Ut.π : D.host.E) ^ d) -
      e * (incA D ((Ut.π : D.host.E))⁻¹ ^ d + incA D (Ut.π : D.host.E) ^ d) + (e - 1)) * hee
  ·
    have hdet := det_transport V h α C _ hC
    have hε' := hε _ (prV_det_eta (D := D) n v Ut.hπ0 d)
    rw [mul_sub, sub_eq_zero, prod_diag_inv n Ut.π d hd, Formalism.L2.Col.mhlA_inv Ut, ← hdet] at hε'
    have key : e * (Formalism.L2.Theta.mt V α⁻¹).det = e * incA D ((((Ut.π : D.host.E))⁻¹ *
        ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) ^ d) :=
      idem_eq_of_swap he.1 hε'
    have hc : incA D ((((Ut.π : D.host.E))⁻¹ * ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) ^ d) =
        incA D ((Ut.π : D.host.E))⁻¹ ^ d * incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E) ^ d :=
      hom_mul_pow (incA D) _ _ d
    exact final_alg hee key hc

end GlobalTheory.Mem.R3.LiftBrg.EtaDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdentityIntegralUnitaryFrameCoordinatesOfUnitGra
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

namespace GlobalTheory.Mem.R3.LiftBrg

theorem castGL_mem_UA_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {m n : ℕ} (h : m = n) (x : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    castGL h x ∈ Formalism.L2.DIV.UA hc (1 : Matrix (Fin n) (Fin n) E) ↔
      x ∈ Formalism.L2.DIV.UA hc (1 : Matrix (Fin m) (Fin m) E) := by
  subst h
  have : castGL (rfl : m = m) x = x := by
    ext i j
    rfl
  rw [this]

theorem frameOK_one_of_gram_eq_one (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (i : Fin X.toD7.R.m) (t : TupU I U) (hg : (Vc X.toD7 i).gram = 1) : LiftBrg.FrameOK X I U i t 1 1 := by
  refine ⟨⟨1, (map_one _).symm⟩, one_mem _, fun x => ?_, one_mem _, one_mem _, fun PP _ => ?_⟩
  · rw [hg, one_mul, inv_one, mul_one]
    exact (castGL_mem_UA_one X.toD7.sp.cm (rkEq X i) x).symm
  · rw [one_mul]; exact one_mem _

end GlobalTheory.Mem.R3.LiftBrg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIrreducibleBaseChangeWeightTensorDualRepOfEmbeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIrreducible_baseChange_weightTensorDualRepOfEmbeddings : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → ∀ (K' : Type) [Field K'] [Algebra K K'],
      (Formalism.IndefR.NX.bcRep (K' := K') (GlobalTheory.AlgWtF.wtRepF emb lam)).IsIrreducible := by
  first | exact @GlobalTheory.AlgWtBC.isIrreducible_bcRep_wtRepF | exact GlobalTheory.AlgWtBC.isIrreducible_bcRep_wtRepF | (intros; apply GlobalTheory.AlgWtBC.isIrreducible_bcRep_wtRepF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotypicHeckeOperatorHyperspecialActsByScalarStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypic_heckeOperator_hyperspecial_acts_by_scalar : ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (Mr : MtReal D μ j) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))), NG.IsProdLevel Mr.J → NG.HypOutside Mr.J Mr.χ B → ∀ (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)), NG.IsIrrRep Mr.wt.ρ S → ∀ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ), s.v ∉ B → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∃ c : ℂ, ∀ y ∈ (NG.isoTyp Mr.wt.ρ S).comap Mr.real, NG.tN Mr.J s ϖ k (Mr.real y) = c • Mr.real y := by
  first | exact @GlobalTheory.IsoTypScalar.main | exact GlobalTheory.IsoTypScalar.main | (intros; apply GlobalTheory.IsoTypScalar.main <;> assumption)
end

