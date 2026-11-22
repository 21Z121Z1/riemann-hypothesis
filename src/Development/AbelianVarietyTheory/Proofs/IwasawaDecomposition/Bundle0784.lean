import Mathlib
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0745
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0766
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0773
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0307
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0415
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0782
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModule
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0989
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0032
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0765
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0748
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0730
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0757
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0755
import Formalism.DegreeFormula.PointDegree.PowSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0717
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyPtsOfReading
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricGramHolomorphicFrameForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0732
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0772

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.G0LiftUnitaryCentralFrame
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.BlockLiftFrame

open ReciprocityTheory.Aut GlobalTheory.CenFrame

section Local

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem exists_isCompOf (s : SplitPlace L) {κ : Formalism.AUTREP.GAf L n} (hκ : κ ∈ Umax L n) :
    ∃ y : GL (Fin n) (Os s), IsCompOf s κ y := by
  obtain ⟨y, hy⟩ := GlobalTheory.TSetDoubleCoset.loc_mem_GLint s hκ
  refine ⟨y, fun a c => ?_⟩
  rw [← hy]
  rfl

theorem isCompOf_one_of_not_mem (s : SplitPlace L) {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}
    (h : s.v ∉ T) {x : Formalism.AUTREP.GAf L n} (hx : TrivOutside T x) : IsCompOf s x 1 := by
  have e : s.loc n x = 1 := by
    apply Units.ext
    refine Matrix.ext fun a b => ?_
    have hc : compAt L s.v (((x : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) a b - (1 : Matrix (Fin n) (Fin n) (AL L)) a b) = 0 := by
      have := congrFun (congrFun (hx s.v h) a) b
      rw [Matrix.map_apply] at this
      rw [map_sub, this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h0 := GlobalTheory.SplitProj.proj_eq_zero_of_compAt_eq_zero L s _ hc
    rw [map_sub, sub_eq_zero] at h0
    show s.proj (((x : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) a b) =
      (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b
    rw [h0, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  intro a c
  rw [e]
  by_cases hac : a = c <;> simp [Matrix.one_apply, hac]

theorem isBlockDiagonal_reduction_of_blockLift_splitPlace (s : SplitPlace L) {r p : ℕ} [NeZero p] (γ : GL (Fin r) (ZMod p)) {κ : Formalism.AUTREP.GAf L n}
    {y : GL (Fin n) (Os s)} (hy : IsCompOf s κ y) (hl : GlobalTheory.PendOf.IsLiftAt s r p γ (s.loc n κ)) {k : Type} [CommRing k]
    (φ : Os s →+* k) (hφ : IsResidue s φ) (i : ZMod p →+* k) :
    GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (Formalism.UG.bc i γ) (Matrix.GeneralLinearGroup.map φ y) := by
  intro a b
  have hl' := hl a b
  have hyab := hy a b
  show φ (y.val a b) = _
  by_cases hab : a.val < r ∧ b.val < r
  · rw [dif_pos hab] at hl' ⊢
    show φ (y.val a b) = i ((γ : Matrix (Fin r) (Fin r) (ZMod p)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩)
    set m : ℕ := ((γ : Matrix (Fin r) (Fin r) (ZMod p)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩).val with hm
    have h0 : φ (y.val a b - (m : Os s)) = 0 := by
      rw [hφ.ker]
      push_cast
      rw [hyab]
      exact hl'
    rw [map_sub, sub_eq_zero, map_natCast] at h0
    rw [h0, ← map_natCast i m, hm, ZMod.natCast_zmod_val]
  · rw [dif_neg hab] at hl' ⊢
    have h1 : ((y.val a b : Os s) : s.v.adicCompletion (maximalRealSubfield L)) = if a = b then 1 else 0 := by
      rw [hyab]; exact hl'
    split_ifs at h1 ⊢ with hab'
    · have h2 : y.val a b = 1 := Subtype.ext (by simpa using h1)
      rw [h2, map_one]
    · have h2 : y.val a b = 0 := Subtype.ext (by simpa using h1)
      rw [h2, map_zero]

end Local

theorem not_mem_gPl_of_twist (D : D7) {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q) (s : SplitPlace D.host.E)
    (hs : s.w ∈ Q) : s.v ∉ GlobalTheory.PendOf.gPl D := by
  rintro ⟨kv, hov⟩
  obtain ⟨q, hq, hcard, -, hqg⟩ := (hQ s.w hs).1
  have hg : (D.host.g kv.1 : 𝓞 D.host.E) ∈ s.w.asIdeal := by
    have h0 : (D.host.g kv.1 : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := D.naut.plGw_over kv.1 kv.2
    have h1 : ((D.host.g kv.1 : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← hov, Ideal.mem_comap, map_natCast]; exact h0
    rw [← s.w_under, Ideal.mem_comap, map_natCast] at h1
    exact h1
  exact GlobalTheory.LevelTypePlace.not_two_primes s.w.asIdeal (D.host.g_prime kv.1) hq (hqg kv.1).symm hg
    (GlobalTheory.LevelTypePlace.natCast_mem_of_card s.w hcard hq.ne_zero)

theorem exists_blockLift (D : D7) {Q Pg : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q) {G : Type} [Group G]
    (eG : G ≃* G0 Pg D.R.r) (cG : G0 Pg D.R.r ≃* G0g D.nd)
    (hgrp : ∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ Pg)
      (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
      (∀ kv, ((plg kv : Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧
      ∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv)) :
    ∃ L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV,
      GlobalTheory.PendOf.IsTypeGroupBlockLift D D.R.nV L ∧ (∀ g, L g ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) ∧
      ∀ g (s' : SplitPlace D.host.E) (φ : Os s' →+* kP s'.w), IsResidue s' φ →
        (s'.w ∈ Q → ∃ y, IsCompOf s' (L g) y ∧ Matrix.GeneralLinearGroup.map φ y = 1) ∧
        ∀ hP : s'.w ∈ Pg, ∃ y, IsCompOf s' (L g) y ∧
          GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (eG ((eG.trans cG).symm g) ⟨s'.w, hP⟩) (Matrix.GeneralLinearGroup.map φ y) := by
  obtain ⟨plg, iso, hpl, hg⟩ := hgrp
  obtain ⟨L, hL, hU⟩ := GlobalTheory.LiftStandardGroup.main D D.R.nV (by unfold Ranks.nV; omega)
  refine ⟨L, hL, hU, fun g s' φ hφ => ⟨fun hs => ?_, fun hP => ?_⟩⟩
  · exact ⟨1, isCompOf_one_of_not_mem s' (not_mem_gPl_of_twist D hQ s' hs) (hL g).1, map_one _⟩
  · obtain ⟨y, hy⟩ := exists_isCompOf s' (hU g)
    refine ⟨y, hy, ?_⟩
    have hkv : plg (plg.symm ⟨s'.w, hP⟩) = ⟨s'.w, hP⟩ := plg.apply_symm_apply _
    have key : ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (PP : Pg), plg kv = PP →
        ∃ i : ZMod (D.host.g kv.1) →+* kP PP.1, eG ((eG.trans cG).symm g) PP = Formalism.UG.bc i (g kv) := by
      intro kv PP hPP
      subst hPP
      exact ⟨iso kv, by rw [hg, MulEquiv.apply_symm_apply]⟩
    obtain ⟨i, hi⟩ := key _ _ hkv
    rw [hi]
    have hw : s'.w = D.naut.plGw (plg.symm ⟨s'.w, hP⟩).1 (plg.symm ⟨s'.w, hP⟩).2 := by
      rw [← hpl, hkv]
    haveI : NeZero (D.host.g (plg.symm ⟨s'.w, hP⟩).1) := ⟨(D.host.g_prime _).ne_zero⟩
    exact isBlockDiagonal_reduction_of_blockLift_splitPlace s' (g _) hy ((hL g).2 _ s' hw) φ hφ i

end GlobalTheory.BlockLiftFrame

end

theorem GlobalTheory.BlockLiftFrame.atMem : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ _ =>
  ∀ s, ∃ L : G0g (w.st Z).toD7.nd → Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
    GlobalTheory.PendOf.IsTypeGroupBlockLift (w.st Z).toD7 (w.st Z).toD7.R.nV L ∧ (∀ g, L g ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV) ∧
    ∀ g (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w), GlobalTheory.CenFrame.IsResidue s' φ →
      (s'.w ∈ t.r.z.R.Q s → ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧ Matrix.GeneralLinearGroup.map φ y = 1) ∧
      ∀ hP : s'.w ∈ t.r.z.R.Pg, ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧
        GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (t.r.z.R.eG ((t.r.z.R.eG.trans t.r.z.cG).symm g) ⟨s'.w, hP⟩) (Matrix.GeneralLinearGroup.map φ y) := by
  intro hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE hR hP => ?_
  intro s
  obtain ⟨plg, iso, h1, -, -, h4⟩ := t.r.z.pins.keep.grp
  exact GlobalTheory.BlockLiftFrame.exists_blockLift (w.st Z).toD7 (t.r.z.lev.is.Q_pl s) t.r.z.R.eG t.r.z.cG ⟨plg, iso, h1, h4⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodFiberTypesAll
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.GoodFirst

set_option maxHeartbeats 2000000 in

theorem goodFTAll_stA (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (hDZ : GlobalTheory.Published.DepthZeroInertia)
    (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (a : StA hL D cf rep) (hlab : GlobalTheory.CoefDuty.OPinModel.LabFixed D)
    (hloc : ∀ (I : GlobalTheory.TypeRec.Ident D) cp, GlobalTheory.TypeRec.IsComp I rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (ρ : Representation ℂ (G0g D.nd) V) (W : Submodule ℂ V) (x : V),
      (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧
        (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom D.ntypes.e0 x = x) : GoodFTAll D := by
  refine GlobalTheory.T.labels_of_depth_zero hG hZ hL D a.A.wdT a.A.row rep
    (fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) a.row a.depth hlab
    (fun k => @GlobalTheory.DepthZeroCusp.depthZeroCuspidal (D.host.g k) ⟨D.host.g_prime k⟩) ?_ hloc
  intro I rc hrc k v
  refine GlobalTheory.TameRecord.tameParam_record hDZ hL D a.A.wdT I rc hrc (fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) k v (a.A.grp.kv k v) ?_
  rw [← a.zeta k]
  exact a.A.grp.tg_tame k v

set_option maxHeartbeats 2000000 in

theorem goodFTAll_allSt : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ _ x => LA hL x → GoodFTAll (Dof x) := by
  intro hP hL
  have h := GlobalTheory.HeightCounting.Up.RowModel.overRows_allSt (GlobalTheory.T.conjugate_vector_in_subspace hP)
  refine EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp fo tr w s P x l => ?_
  have hloc := H kp fo tr w s P x
  have ty : TypesTrue (Dof x).ntypes (Fr.at (w.st x.o.Z) f).P (Fr.at (w.st x.o.Z) f).W := x.fits.grp
  exact goodFTAll_stA hP.green hP.zel hP.dz hL (Dof x) (cfOf x) (repOf x.r.Y) l.a
    (GlobalTheory.CoefDuty.OPinModel.labFixed_of_typesTrue ty) hloc

end GlobalTheory.GoodFirst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodRowsSameEigenvaluesSameFrobeniusStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_rows_same_eigenvalues_same_frobenius : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (Sb : Finset (PlE D.host)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0), GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ σ σ' : D.what₂.FT, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → D.what₂.isot j σ' ≠ ⊥ → D.nd.goodRow σ' → ∀ P : PlE D.host, IsSplitPl D.host P → P ∉ Sb → (∀ k, 1 ≤ k → k ≤ D.R.r → eig j σ' k P = eig j σ k P) → D.naut.frobEig (Rw.locR σ' P) = D.naut.frobEig (Rw.locR σ P) := by
  first | exact @GlobalTheory.FrobSame.frobEig_eq_of_eig_eq | exact GlobalTheory.FrobSame.frobEig_eq_of_eig_eq | (intros; apply GlobalTheory.FrobSame.frobEig_eq_of_eig_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductIntegralEqFlagDegreeWeight
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

namespace GlobalTheory.GrassTop

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rho_eq_flagMap (H : Host E) (Dw : Datum H) : rho H Dw = GlobalTheory.Schubert.flagMap Dw := rfl

theorem degFl_rho_antisymm (H : Host E) (Dw : Datum H) (Q : MvPolynomial (Root Dw.mult) ℝ) :
    Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (rho H Dw (antisymm Q)) =
      (∏ τ, ((Dw.mult τ).factorial : ℝ)) * Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (rho H Dw Q) := by
  rw [rho_eq_flagMap]
  unfold GlobalTheory.GoodMetric.antisymm
  rw [map_sum, ← GlobalTheory.Schubert.flagLin_apply, map_sum]
  have hterm : ∀ w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ)),
      GlobalTheory.Schubert.flagLin (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (GlobalTheory.Schubert.flagMap Dw
        ((((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ)) • rename (fun x : Root Dw.mult =>
          (⟨x.1, w x.1 x.2⟩ : Root Dw.mult)) Q)) =
        Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (GlobalTheory.Schubert.flagMap Dw Q) := by
    intro w
    rw [map_zsmul, map_zsmul, GlobalTheory.Schubert.flagLin_apply,
      GlobalTheory.Schubert.degFl_flagMap_rename_perm, zsmul_eq_mul, ← mul_assoc]
    have hs : ((((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ)) *
        (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
    rw [hs, one_mul]
  rw [Finset.sum_congr rfl fun w _ => hterm w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_pi]
  push_cast
  simp only [Fintype.card_perm, Fintype.card_fin]

theorem prod_factorial_mult (H : Host E) (Dw : Datum H) :
    (∏ τ, ((Dw.mult τ).factorial : ℝ)) =
      ((Dw.p.factorial * Dw.q.factorial : ℝ)) ^ Fintype.card (GlobalTheory.AllWt.Psi H) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]
  have e1 : ∀ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}, ((Dw.mult τ.1).factorial : ℝ) = Dw.p.factorial := by
    intro τ; simp [Datum.mult, τ.2]
  have e2 : ∀ τ : {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0}, ((Dw.mult τ.1).factorial : ℝ) = Dw.q.factorial := by
    intro τ; simp [Datum.mult, τ.2]
  simp only [e1, e2, Finset.prod_const, Finset.card_univ, mul_pow]
  congr 2
  exact Fintype.card_congr
    { toFun := fun τ => (⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩ : GlobalTheory.AllWt.Psi H)
      invFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩
      left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1)
      right_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1) }

theorem intGr_eq_flagDeg : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) (D : ℕ),
    D = Fintype.card (GlobalTheory.AllWt.Psi H) * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) →
    antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ D) =
      chernRoots Dw.mult R * rootDiscr Dw.mult →
    intGr H Dw R = Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ)) := by
  intro E _ _ _ H Dw la R D hD hA
  unfold intGr
  rw [← hA, degFl_rho_antisymm, prod_factorial_mult, map_pow, rho_eq_flagMap,
    GlobalTheory.Schubert.chernRootSubstitution_weightLineBundle_eq_linRoot, hD]
  have hpos : ((Dw.p.factorial * Dw.q.factorial : ℝ)) ^ Fintype.card (GlobalTheory.AllWt.Psi H) ≠ 0 := by
    apply pow_ne_zero; exact_mod_cast (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)).ne'
  rw [mul_div_cancel_left₀ _ hpos]
  rfl

end GlobalTheory.GrassTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductIntegralEqZeroOfMemRelIdeal
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

namespace GlobalTheory.GrassTop.RelVanish

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rho_eq_flagMap (H : Host E) (Dw : Datum H) : rho H Dw = GlobalTheory.Schubert.flagMap Dw := by
  unfold rho GlobalTheory.Schubert.flagMap
  congr 1

noncomputable def numLin (H : Host E) (Dw : Datum H) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ :=
  GlobalTheory.Schubert.flagLin (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) ∘ₗ (GlobalTheory.Schubert.flagMap Dw).toLinearMap ∘ₗ
    LinearMap.mulRight ℝ (rootDiscr Dw.mult) ∘ₗ (chernRoots Dw.mult).toLinearMap

theorem numLin_apply (H : Host E) (Dw : Datum H) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) :
    numLin H Dw Q = Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q)
      (GlobalTheory.Schubert.flagMap Dw (chernRoots Dw.mult Q * rootDiscr Dw.mult)) := by
  simp [numLin, GlobalTheory.Schubert.flagLin_apply]

theorem numLin_of_chernRoots_eq_zero (H : Host E) (Dw : Datum H) (g : MvPolynomial ((E →+* ℂ) × ℕ) ℝ)
    (hg : chernRoots Dw.mult g = 0) (a : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) : numLin H Dw (g * a) = 0 := by
  rw [numLin_apply, map_mul (chernRoots Dw.mult), hg, zero_mul, zero_mul, map_zero, ← GlobalTheory.Schubert.flagLin_apply, map_zero]

theorem chernRoots_X_zero_sub_one (H : Host E) (Dw : Datum H) (τ : E →+* ℂ) :
    chernRoots Dw.mult (X (τ, 0) - 1 : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) = 0 := by
  simp [chernRoots, esymm_zero]

theorem chernRoots_X_of_lt (H : Host E) (Dw : Datum H) (τ : E →+* ℂ) (k : ℕ) (hk : Dw.mult τ < k) :
    chernRoots Dw.mult (X (τ, k) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) = 0 := by
  have h0 : esymm (Fin (Dw.mult τ)) ℝ k = 0 := by
    unfold esymm
    rw [Finset.powersetCard_eq_empty.mpr (by simpa using hk)]
    simp
  simp [chernRoots, h0]

theorem numLin_relPoly (H : Host E) (Dw : Datum H) (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) (hk : 1 ≤ k)
    (a : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) : numLin H Dw (GlobalTheory.PointChern.relPoly τ k * a) = 0 := by
  rw [numLin_apply, map_mul (chernRoots Dw.mult), mul_assoc, map_mul, GlobalTheory.Schubert.RelKill.flagMap_relPoly]
  exact Formalism.DegreeFormula.degreeEsymmMulEqZero _ _ τ k _ hk

theorem numLin_mul_eq_zero (H : Host E) (Dw : Datum H) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ)
    (hQ : Q ∈ relIdeal H Dw) : ∀ a, numLin H Dw (Q * a) = 0 := by
  unfold relIdeal at hQ
  induction hQ using Submodule.span_induction with
  | mem x hx =>
    intro a
    rcases hx with (⟨τ, rfl⟩ | ⟨τ, k, hk, rfl⟩) | ⟨τ, k, hk, rfl⟩
    · exact numLin_of_chernRoots_eq_zero H Dw _ (chernRoots_X_zero_sub_one H Dw τ) a
    · exact numLin_of_chernRoots_eq_zero H Dw _ (chernRoots_X_of_lt H Dw τ k hk) a
    · exact numLin_relPoly H Dw τ k hk a
  | zero => intro a; simp
  | add x y _ _ hx hy => intro a; rw [add_mul, map_add, hx, hy, add_zero]
  | smul r x _ hx => intro a; rw [smul_eq_mul, mul_assoc, mul_comm r, mul_assoc]; exact hx _

end GlobalTheory.GrassTop.RelVanish

namespace GlobalTheory.GrassTop

theorem intGr_eq_zero_of_mem_relIdeal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), Q ∈ relIdeal H Dw → intGr H Dw Q = 0 := by
  intro E _ _ _ H Dw Q hQ
  have h := RelVanish.numLin_mul_eq_zero H Dw Q hQ 1
  rw [mul_one, RelVanish.numLin_apply, ← RelVanish.rho_eq_flagMap] at h
  rw [intGr, h, zero_div]

end GlobalTheory.GrassTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterSplitPlaceComponentUniqueStatement
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
theorem _root_.GlobalTheory.T.heckeCharacter_splitPlaceComponent_unique : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (χ : HChar L) (s : SplitPlace L) (ξ ξ' : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.IsCompAt χ s ξ → NG.IsCompAt χ s ξ' → ξ = ξ' := by
  first | exact @GlobalTheory.CompAtUniq.main | exact GlobalTheory.CompAtUniq.main | (intros; apply GlobalTheory.CompAtUniq.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeometricAllStatesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_geometric_all_states : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ P x => ∀ (l : SeriesLevel hL x) (i : (Dof x).ntw.Tw) (b : Bool) (j : Fin (Dof x).R.m), GlobalTheory.GeoTie.HeckeGeo l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) b j := by
  first | exact @GlobalTheory.HeightCounting.HeckeLaw.hecke_geometric_of_lb1 | exact GlobalTheory.HeightCounting.HeckeLaw.hecke_geometric_of_lb1 | (intros; apply GlobalTheory.HeightCounting.HeckeLaw.hecke_geometric_of_lb1 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricGramHolomorphicFrameFormStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeMetric_gram_holomorphic_frame_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ k' : U.Comp, ∃ (G : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q) → Mat Dw.mult ℂ) (z : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q) → GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ) (cc : (E →+* ℂ) → ℝ), (∀ τ, 0 < cc τ) ∧ ∀ (x : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)) (hx : x ∈ (U.X k').dom), (∀ τ a b, AnalyticAt ℂ (fun x' => G x' τ a b) x) ∧ (∀ τ a b, AnalyticAt ℂ (fun x' => z x' τ a b) x) ∧ (∀ τ, IsUnit (G x τ).det) ∧ InDom (z x) ∧ ∀ τ, ((hodgeMet Z U).gram (cxPt Z (U.un k' ⟨x, hx⟩)) (cxFrame Z (U.un k' ⟨x, hx⟩)) τ)ᵀ = (cc τ : ℂ) • (G x τ * modelGram H Dw (z x) τ * (G x τ)ᴴ) := by
  first | exact @GlobalTheory.HodgeGramGen.hodge_gram_frame | exact GlobalTheory.HodgeGramGen.hodge_gram_frame | (intros; apply GlobalTheory.HodgeGramGen.hodge_gram_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricSmoothOffBoundaryStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_metric_smooth_off_boundary : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), (x.hodge σ).SmoothOn (manifold s.T.Z σ) {y | ¬ LiesIn y (genBd s.T.Z)} := by
  first | exact @GlobalTheory.ShFam.ToroidalCompactificationData.hodge_smoothOn | exact GlobalTheory.ShFam.ToroidalCompactificationData.hodge_smoothOn | (intros; apply GlobalTheory.ShFam.ToroidalCompactificationData.hodge_smoothOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCoverNormalProjectiveChartsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCover_normal_projective_charts : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Field K] [Algebra O K] [IsFractionRing O K] (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover (algebraMap O K) s V α c D → ∃ (n : ℕ) (I : (PSpace O n).IdealSheafData) (π : I.subscheme ⟶ X) (g : ∀ en : En m, I.subscheme ⟶ PSpace O (plN M en.1)) (κ : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ I.subscheme)), π ≫ s = I.subschemeι ≫ PSpace.str O n ∧ IsFlagModel (algebraMap O K) s V α c π g κ := by
  first | exact @GlobalTheory.FlagModel.exists_flagModel | exact GlobalTheory.FlagModel.exists_flagModel | (intros; apply GlobalTheory.FlagModel.exists_flagModel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyFanOfStarSubdivisionCells
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarFan

theorem homog_of_cover : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], (∀ B ∈ psdCone bar X, ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell bar φ γ ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i)) → ∀ B ∈ psdCone bar X, ∀ t : ℝ, 0 ≤ t → evalR φ (t • B) = t * evalR φ B := by
  intro O _ bar φ X _ _ _ hcov B hB t ht
  obtain ⟨e, m, γ, c, hγ, hc, he⟩ := hcov B hB
  have key : ∀ (B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (c₀ : Fin m → ℝ), (∀ i, 0 ≤ c₀ i) →
      (∀ a b, B₀ (e a) (e b) = ∑ i, c₀ i * (γ i a b : ℝ)) → evalR φ B₀ = ∑ i, c₀ i * φ.evalZ (γ i) :=
    fun B₀ c₀ hc₀ hB₀ => hγ.linear.eval_eq_sum (r := e.toLinearMap) e.surjective hc₀ hB₀
  have hv : ∀ a b, B (e a) (e b) = ∑ i, c i * (γ i a b : ℝ) := fun a b => by
    have := LinearMap.congr_fun₂ he a b
    simpa [LinearMap.sum_apply] using this
  rw [key B c hc hv, key (t • B) (fun i => t * c i) (fun i => mul_nonneg ht (hc i)) fun a b => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, hv, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem isPolyFan_star : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → IsStarOf H.bar q ψ w ψ' → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, ψ'.evalZ β = n) → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ψ'.evalZ β) → IsPolyFan H.bar q ψ' := by
  intro E _ _ _ H q ψ w ψ' hψ hw hst hint hpos X _ _ _ _ hX
  obtain ⟨S, hS, hcov⟩ := GlobalTheory.T.starSubdivision_cells_finite_cover_up_to_aut E H q ψ w ψ' hψ hw hst X hX
  have hcov' : ∀ B ∈ psdCone H.bar X, ∃ (e : X ≃ₗ[𝓞 E] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ),
      IsCell H.bar ψ' γ ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := fun B hB => by
    obtain ⟨e, m, γ, c, h1, -, h3, h4⟩ := hcov B hB
    exact ⟨e, m, γ, c, h1, h3, h4⟩
  exact
    { homog := homog_of_cover (𝓞 E) H.bar ψ' X hcov'
      superadd := GlobalTheory.T.superadditive_of_cells_cover_cone (𝓞 E) H.bar ψ' X hcov'
      integral := hint X hX
      pos := hpos X hX
      finite := ⟨S, hS, hcov⟩ }

end GlobalTheory.PolFan.StarFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProductLevelDefiniteFormsRealisationAtTwistStatement
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
theorem _root_.GlobalTheory.T.isProductLevel_definiteFormsRealisationAtTwist : ∀ (D : D7) (X : NExpTied D) (i : D.ntw.Tw) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m), NG.IsProdLevel (cell X b hA j).J := by
  first | exact @GlobalTheory.LevProd.main | exact GlobalTheory.LevProd.main | (intros; apply GlobalTheory.LevProd.main <;> assumption)
end

