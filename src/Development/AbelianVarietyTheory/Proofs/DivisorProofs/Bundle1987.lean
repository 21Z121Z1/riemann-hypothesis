import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0386
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0034
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0398
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0205
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0688
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0253
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsProductsCosocles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1976
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsVanishingOffFramesLeSpanShortTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0081
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0044
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0077
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0068
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0063
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0003
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1102
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1977
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarModelLocalTriple
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSupportTransport
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LocLanglands GlobalTheory.WeilDeligne GlobalTheory.LocGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GoodTransport

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.FieldTransport GlobalTheory.LocLanglands.TransportGL GlobalTheory.LocLanglands.FieldCompat
  ValuativeRel Matrix

section Pull

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isSubquotient_pull {σ : Representation ℂ H W} {ρ : Representation ℂ H V} (φ : G →* H)
    (h : IsSubquotient σ ρ) : IsSubquotient (pull σ φ) (pull ρ φ) := by
  obtain ⟨S, f, hf⟩ := h
  exact ⟨⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (φ g) hv⟩,
    ⟨f.toLinearMap, fun g => f.isIntertwining' (φ g)⟩, hf⟩

end Pull

section Fields

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k']

theorem hasSupport_transport (i : k ≃+* k') (hi : Continuous i) {x : IrrGL k} {x' : IrrGL k'} (hx : RepRel i x x')
    {s : Multiset (IrrGL k)} (hs : HasSupport x.rep s) :
    ∃ s' : Multiset (IrrGL k'), HasSupport x'.rep s' ∧ ∀ y' ∈ s', ∃ y ∈ s, RepRel i y y' := by
  have T1 := GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k k' i hi
  have hi' : Continuous i.symm := T1.1
  have T2 := GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k' k i.symm hi'
  obtain ⟨T, hT, -⟩ := GlobalTheory.T.transportIrrGL_bijective_degree_charZero k k' i hi
  have hC := (GlobalTheory.LocLanglands.repRel_isCusp_nu_ofChar k k' i hi).1
  obtain ⟨r, xs, rfl, -, hc, e, hsub⟩ := hs
  let σ' : ∀ a, Representation ℂ (GL (Fin (xs a).1) k') (xs a).2.rep.V := fun a =>
    pull (xs a).rep (GeneralLinearGroup.map (i.symm : k' →+* k))
  have hsm : ∀ a, IsSmooth (σ' a) := fun a =>
    isSmooth_comp (xs a).2.rep.smooth (continuous_glMap (i.symm : k' →+* k) hi')
  have hir : ∀ a, (σ' a).IsIrreducible := fun a =>
    (isIrreducible_comp_iff (glMap_surjective i.symm)).2 (xs a).2.rep.irr
  have hrel : ∀ a, RepRel i (xs a) (IrrGL.of (σ' a) (hsm a) (hir a)) := fun a => by
    have h1 := (hT (xs a) (T (xs a))).2 rfl
    have h2 := eq_of_repRel i hi' h1
    rw [h2] at h1
    exact h1
  have hcu : ∀ a, IsCuspidal (σ' a) := fun a =>
    (IrrGL.isCusp_of.1 ((hC _ _ (hrel a)).1.1 ⟨(hc a).1, (hc a).2.2⟩)).2
  obtain rfl := eq_of_repRel i hi' hx
  have B := (nonempty_equiv_parInd e i.symm hi' hi T1.2.2.2.2 T2.2.2.2.2
    (ρ := piTensor σ') (ρ' := piTensor fun a => (xs a).rep) (fun h => by
      show _ = piTensor (fun a => (xs a).rep) (leviMap (i.symm : k' →+* k) (leviMap (i : k →+* k') h))
      rw [leviMap_symm_leviMap])).some
  have hS : IsSubquotient (IrrGL.of (pull x.rep (GeneralLinearGroup.map (i.symm : k' →+* k)))
      (isSmooth_comp x.2.rep.smooth (continuous_glMap (i.symm : k' →+* k) hi'))
      ((isIrreducible_comp_iff (glMap_surjective i.symm)).2 x.2.rep.irr)).rep (multiProd e σ') :=
    (IsSubquotient.of_injective (IrrGL.equivOf _ _ _).symm.toIntertwiningMap
      (IrrGL.equivOf _ _ _).symm.toLinearEquiv.injective).trans
      ((isSubquotient_pull _ hsub).trans
        (IsSubquotient.of_injective B.symm.toIntertwiningMap B.symm.toLinearEquiv.injective))
  have H : IsCuspSupport _ (fun a => (xs a).1) σ' :=
    ⟨IrrRep.irr _, fun a => ⟨(hc a).1, hir a, hcu a⟩, e, hS⟩
  refine ⟨_, hasSupport_of_isCuspSupport H, fun y' hy' => ?_⟩
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hy'
  exact ⟨xs a, Multiset.mem_map_of_mem _ (Finset.mem_univ a), hrel a⟩

theorem goodCusp_transport (i : k ≃+* k') (hi : Continuous i)
    (hfixT : ∀ (z : IrrGL k) (z' : IrrGL k'), RepRel i z z' →
      GlobalTheory.PRep.fixed z.rep (GlobalTheory.SplitWeil.KOne k (Fin z.1)) ≠ ⊥ →
      GlobalTheory.PRep.fixed z'.rep (GlobalTheory.SplitWeil.KOne k' (Fin z'.1)) ≠ ⊥)
    {y : IrrGL k} {y' : IrrGL k'} (hy : RepRel i y y')
    (h : UpperTheory.Zero.LLC.GoodCusp y) : UpperTheory.Zero.LLC.GoodCusp y' := by
  have hi' : Continuous i.symm := (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k k' i hi).1
  obtain ⟨T, hT, hTd⟩ := GlobalTheory.T.transportIrrGL_bijective_degree_charZero k k' i hi
  obtain rfl : T y = y' := (hT _ _).1 hy
  rcases h with h1 | ⟨⟨g, hg, j, hj⟩, y₀, χ, hχ, hfix, rfl⟩
  · left
    rw [hTd]
    exact h1
  · right
    have hv : ∀ z, (χ.comp (Units.map i.symm.toRingHom.toMonoidHom)) (Units.map i.toRingHom.toMonoidHom z) = χ z :=
      fun z => congrArg χ (Units.ext (by simp))
    refine ⟨⟨g, hg, j.trans i, hi.comp hj⟩, T y₀, χ.comp (Units.map i.symm.toRingHom.toMonoidHom),
      isSmoothChar_comp i.symm hi' hχ, hfixT _ _ ((hT _ _).2 rfl) hfix, ?_⟩
    apply (hT _ _).1
    obtain ⟨n, π, π', e, h1, h2, he⟩ := (hT y₀ (T y₀)).2 rfl
    rw [h2, h1]
    exact repRel_tw i π π' e he χ hχ _ _ hv

end Fields

theorem good_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'),
    Continuous i → ∀ (x : GlobalTheory.LocGL.IrrGL k) (x' : GlobalTheory.LocGL.IrrGL k'), GlobalTheory.LocLanglands.RepRel i x x' →
      UpperTheory.Zero.LLC.Good x → UpperTheory.Zero.LLC.Good x' := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi x x' hx ⟨s, hs, hg⟩
  obtain ⟨s', hs', hrel⟩ := hasSupport_transport i hi hx hs
  exact ⟨s', hs', fun y' hy' => let ⟨y, hy, h⟩ := hrel y' hy'
    goodCusp_transport i hi (GlobalTheory.FixedKOneTransport.fixed_kOne_transport k k' i hi) h (hg y hy)⟩

end GlobalTheory.GoodTransport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RawSpan

section Cover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

abbrev idCover (nab : NabV Xo c) (n : ℕ) : DeltaDat Xo c n := noDelta Xo c nab (GlobalTheory.ObjLower.sabId Xo.univ.t) n

theorem frOver_self (nab : NabV Xo c) (n : ℕ) {S : Type} [CommRing S] [i : Algebra c.F S] (y : FrPt Xo c S) :
    @FrOver E _ _ _ H Dw l Xo c n (idCover nab n) S _ i i y y := by
  refine (@GlobalTheory.FrameLift.frOver_iff E _ _ _ H Dw l Xo S _ c n (idCover nab n) i i y y).2
    ⟨Category.comp_id _, fun _ _ => Category.comp_id _, GlobalTheory.ObjLower.idIso Xo.univ.t.PP.L, 𝟙 _,
      ⟨(isGen_iff _).2 (GlobalTheory.ObjLower.pgen_idIso Xo.univ.t.PP.isLB), ?_⟩,
      (Category.id_comp _).trans (Category.comp_id _).symm, Category.id_comp _, ?_⟩
  · exact (maps_iff (GlobalTheory.ObjLower.idIso Xo.univ.t.PP.L) _ (fun _ => eSec Xo.univ.t.G) _ Xo.univ.t.PP.rig
      Xo.univ.t.PP.rig (GlobalTheory.ObjLower.cubeId Xo.univ.t.G).e _
      (rigPull_le (GlobalTheory.ObjLower.cubeId Xo.univ.t.G).F (GlobalTheory.ObjLower.cubeId Xo.univ.t.G).e
        (GlobalTheory.ObjLower.cubeId Xo.univ.t.G).e_comm Xo.univ.t.PP.L) (fun _ => rfl)).2
      (GlobalTheory.ObjLower.pmaps_idIso _ _ _ _ Xo.univ.t.PP.rigGen)
  · intro Z r z i j hi hj
    have e := GlobalTheory.ObjLower.gw_idIso Xo.univ.t.PP.L (r ≫ (snd (Over.mk y.x) Xo.univ.t.G).left) z i j hi hj
    have e' := GlobalTheory.FrameLift.sv_trans (q := (snd (Over.mk y.x) Xo.univ.t.G).left) y.s r z hi hj
    exact (congrArg (fun t => GlobalTheory.FrameLift.sv (q := (snd (Over.mk y.x) Xo.univ.t.G).left) y.s t z i)
      (Category.comp_id r)).trans (e'.trans (congrArg (fun u : (Z.presheaf.stalk z)ˣ => u.val * _) e.symm))

theorem evR_one_field (S : Type) [Field S] [Algebra c.F S] (y : FrPt Xo c S) : evR Xo c 1 y = 1 :=
  evalAt_one _ _ y (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c S y)

theorem idCover_isLev (nab : NabV Xo c) (n : ℕ) : (idCover nab n).IsLev := by
  refine ⟨⟨dvd_rfl, le_rfl, dvd_rfl⟩, (Nat.mul_one _).symm, Nat.coprime_one_left _, (Ideal.mul_top _).symm,
    top_sup_eq _, ?_, ?_, GlobalTheory.LevelCover.one_mem_sec_zero Xo c, ?_⟩
  · rw [GlobalTheory.LevelCoverDatum.noDelta_etaOK]
    exact ⟨fun a => Category.comp_id _, fun a => Category.comp_id _⟩
  · intro k _ _ i₁ i₂ hk y
    have e : i₂ = i₁ := Algebra.algebra_ext _ _ fun a => hk a
    rw [e]
    exact ⟨y, @frOver_self E _ _ _ H Dw l Xo c nab n k _ i₁ y⟩
  · intro k _ _ i y₂
    have := @evR_one_field E _ _ _ H Dw l Xo c k _ i y₂
    exact fun h => one_ne_zero (this.symm.trans h)

theorem idCover_unitC (nab : NabV Xo c) (n : ℕ) : GlobalTheory.Dict.UnitC (idCover nab n) := fun A y =>
  (congrArg norm (@evR_one_field E _ _ _ H Dw l Xo c ℂ _ A y)).trans norm_one

theorem idCover_psiTie (nab : NabV Xo c) (n : ℕ) : (idCover nab n).PsiTie 1 := by
  intro k g ρ _ _ _ _ K _ _ i y y' _
  have a := @evR_one_field E _ _ _ H Dw l Xo c K _ i y
  have b := @evR_one_field E _ _ _ H Dw l Xo c K _ i y'
  refine b.trans ?_
  refine Eq.symm ((congrArg _ a).trans ?_)
  simp

theorem betaH_ne_zero {n : ℕ} (Λ : GenLat E n) : betaH (Dw := Dw) c Λ ≠ 0 := by
  unfold betaH
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

theorem phiHat_indPhi_mk {n : ℕ} (x0 : Fin n → Dw.La) :
    phiHat c (indPhi c fun b => (Submodule.Quotient.mk (x0 b) : LevQc Dw l)) = x0Dat c x0 := by
  have h : phiHat c (indPhi c fun b => (Submodule.Quotient.mk (x0 b) : LevQc Dw l)) =
      x0Dat c fun b => qRep (Submodule.Quotient.mk (x0 b) : LevQc Dw l) := by
    funext q
    unfold phiHat x0Dat indPhi
    rw [finsum_eq_single _ (fun b => (Submodule.Quotient.mk (x0 b) : LevQc Dw l)) (fun x hx => by simp [hx])]
    simp
  rw [h, GlobalTheory.LevelPairing.levelFourierDatum_eq_iff]
  intro b
  exact (Submodule.Quotient.eq _).1 (Classical.choose_spec (Submodule.Quotient.mk_surjective _
    (Submodule.Quotient.mk (x0 b) : LevQc Dw l)))

theorem span_mk_eq_top {n : ℕ} (x0 : Fin n → Dw.La) (h : AdmX (l := l) true x0) :
    Submodule.span (𝓞 E) (Set.range fun b => (Submodule.Quotient.mk (x0 b) : LevQc Dw l)) = ⊤ := by
  unfold AdmX at h
  rw [sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, Set.image_image] at h
  rw [← h]
  congr 1
  ext z
  simp

theorem thLaValAt_of_isShortRule [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) {n : ℕ} {Λ : GenLat E n} {N : ℕ}
    (hU : Λ.Unimod) (hT : Λ.TrivAt l.M) (hO : Λ.LevOK N l.M) {a : (E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmL c Λ a) (x0 : Fin n → Dw.La) {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) (h : IsShortRule Xo c (idCover nab n) Λ N x0 P f) (p : TRing c.F) (y : FrPt Xo c p.R) :
    thLaValAt Xo c nab (x0Dat c x0) Λ N P y ((betaH (Dw := Dw) c Λ • f) p y) := by
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  haveI : _root_.IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  obtain ⟨hval, hnat⟩ := GlobalTheory.shortThetaValue_existsUnique_natural hL GlobalTheory.chartIndependence_unconditional E H Dw l Xo c
    nab hnab n Λ N hU hT hO a P hP.1 (x0Dat c x0) (betaH (Dw := Dw) c Λ)
  obtain ⟨v, hv, -⟩ := hval p.R y
  have e : f p y = v := by
    refine GlobalTheory.CoverDescent.eq_of_geometric_points _ _ fun k _ _ χ => ?_
    letI i1 : Algebra c.F k := (χ.comp (algebraMap c.F p.R)).toAlgebra
    let χa : p.R →ₐ[c.F] k := { χ with commutes' := fun _ => rfl }
    obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c p.R k χa y
    obtain ⟨u, hu, eu⟩ := @h k _ _ i1 i1 (fun _ => rfl) z z (frOver_self nab n z)
    have hu' : ShortValAt Xo c nab (x0Dat c x0) Λ (betaH (Dw := Dw) c Λ) N P z u := by
      have e1 : MvPolynomial.map ((idCover nab n).eF : c.F →+* (idCover nab n).c₂.F) P = P := MvPolynomial.map_id P
      rw [e1, GlobalTheory.LevelCoverDatum.noDelta_w] at hu
      exact hu
    have e2 := hnat p.R k χa y z hz v u hv hu'
    have e3 := GlobalTheory.CoverDescent.evR_of_test (GlobalTheory.Frames.algebraic_laws hL.secBaseChange E H Dw l Xo c).2.2.1 f hf.1
      p χa y z hz
    have e4 : evR Xo c f z = u := eu.trans ((congrArg (· * u) (evR_one_field k z)).trans (_root_.one_mul u))
    exact e3.symm.trans (e4.trans e2.symm)
  have e5 : (betaH (Dw := Dw) c Λ • f) p y = algebraMap c.F p.R (betaH (Dw := Dw) c Λ) * v := by
    rw [← e]
    exact Algebra.smul_def (betaH (Dw := Dw) c Λ) (f p y)
  rw [e5]
  exact (GlobalTheory.Survey.BaseClassMove.shortValAt_beta Xo c nab _ Λ _ (betaH_ne_zero Λ) N P y v).1 hv

end Cover

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 1000000 in

theorem holSub0_le_span_raw : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.Pj.Unf Xo c σ r), Formalism.L2.Pj.GoodEmb c σ → Formalism.L2.Pj.IsUnf U → 1 ≤ r → l.A = 1 → (∀ k k', (U.X k).Gm = (U.X k').Gm ∧ (U.X k).ξ0 = (U.X k').ξ0) → (∀ k, GlobalTheory.Dict.HasPrinc (U.X k) l.M) → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (bad n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < bad → Dom a n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, GlobalTheory.Dict.ChiOne (U.X k) (Formalism.L2.Pj.laU U a n k)) → Formalism.L2.Pj.holSub0 U.X (Formalism.L2.Pj.laU U a n) ≤ Submodule.span ℂ (Formalism.L2.Pj.rdU U '' ⋃ (x0 : Fin n → LevQc Dw l) (_ : Submodule.span (𝓞 E) (Set.range x0) = ⊤), {f : Formalism.L2.Pj.Rul Xo c | f ∈ sec Xo c a n ∧ ∃ (La : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F), La.Unimod ∧ La.TrivAt bad ∧ La.TrivAt l.M ∧ La.LevOK N l.M ∧ P ∈ harmL c La a ∧ ∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab (phiHat c (indPhi c x0)) La N P y (f p y)}) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hr hA hG hP _ nab hnab bad n a hbad hdom hn hχ
  have hC := GlobalTheory.chartIndependence_unconditional
  have hrk : r = Dw.p + Dw.q := hU.1
  have h1 : 1 ≤ Dw.p + Dw.q := hrk ▸ hr
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hB : Out.SecBaseChangeSt := hL.secBaseChange
  have hpin := GlobalTheory.DeltaPinTest.noDelta_phiPin (n := n) nab (GlobalTheory.ObjLower.sabId Xo.univ.t)
  have hT := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c
  have hW := (GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1
  have htot : ShortValTot Xo c nab bad n a n (idCover nab n) :=
    GlobalTheory.shortValTot_of_pinned hL hC E H Dw l Xo c n (idCover nab n) (GlobalTheory.levelMaps_closed hL E H Dw h1) hW hT hW hT
      (idCover_isLev nab n) rfl ⟨_, hnab⟩ (fun _ => ⟨_, 1, _, hpin, idCover_psiTie nab n⟩) nab bad n a
  have key := GlobalTheory.Dict.holSub0_le_span_shortGen hC E H Dw l Xo c n (idCover nab n) σ r
    (Formalism.L2.PjFree.Unf.ofPj U) hσ hU hr hA hG hP (idCover_isLev nab n) ⟨_, hnab⟩ (idCover_unitC nab n)
    (by show ¬ 3 ∣ 1; decide) (fun _ => ⟨_, 1, _, hpin⟩) nab bad n a hbad hdom hn hχ htot
  intro Q hQ
  refine Submodule.span_le.2 ?_ (key hQ)
  rintro _ ⟨f, ⟨hf, Λ, N, x0, P, hΛ, hb, hM, hO, hX, hPm, hrule⟩, rfl⟩
  have hβ := betaH_ne_zero (Dw := Dw) (c := c) Λ
  have e : Formalism.L2.PjFree.rdU (Formalism.L2.PjFree.Unf.ofPj U) f =
      (σ (betaH (Dw := Dw) c Λ))⁻¹ • Formalism.L2.Pj.rdU U (betaH (Dw := Dw) c Λ • f) := by
    rw [LinearMap.map_smulₛₗ, smul_smul, inv_mul_cancel₀ ((map_ne_zero σ).2 hβ), one_smul]
    rfl
  rw [e]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
  rw [decide_eq_true (rfl : n = n)] at hX
  refine Set.mem_iUnion₂.2 ⟨fun b => Submodule.Quotient.mk (x0 b), span_mk_eq_top x0 hX,
    Submodule.smul_mem _ _ hf, Λ, N, P, hΛ, hb, hM, hO, hPm, fun p y => ?_⟩
  rw [phiHat_indPhi_mk]
  exact thLaValAt_of_isShortRule nab hnab hΛ hM hO hPm x0 hf hrule p y

end GlobalTheory.RawSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTopOfDictionaryDepth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat

open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

theorem sizes : ∀ (D : D7) (large₂ : SizeData₂ D) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
    1 ≤ Real.log large₂.sc.b ∧ Real.log D.host.rdE ≤ Real.log large₂.sc.b ∧ |logDerivativeAtOne D| ≤ Real.log large₂.sc.b := by
  intro D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS
  obtain ⟨-, hSz, -, -, -, -, -, -, -, hrd, hcond, -⟩ := hS.size
  have hb : Real.log large₂.sc.b = large₂.sc.x ^ large₂.sc.eps := by
    simp [Formalism.BasicNotions.Scale.b, Formalism.BasicNotions.Scale.L]
  have hL1 : 1 ≤ large₂.sc.x ^ large₂.sc.eps := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hqd : |large₂.logDerivativeAtOne| ≤ large₂.sc.x ^ large₂.sc.eps := hSz.2.2.2.2.2.2.1.2.2.2.2.2.1
  have he : large₂.logDerivativeAtOne = logDerivativeAtOne D := by
    rw [large₂.logDerivative_at_one_eq]
    rfl
  rw [hb]
  refine ⟨hL1, ?_, he ▸ hqd⟩
  have : Real.log D.host.rdE ≤ large₂.sc.L / 100 := hrd.trans hcond
  simp only [Formalism.BasicNotions.Scale.L] at this
  linarith

theorem meanInf_affine (K : Type) [Field K] [NumberField K] (a0 nD Gd : ℝ) (f g : InfinitePlace K → ℝ) (ha0 : 0 ≤ a0) :
    Formalism.PairingDivisionLocalBalance.meanInf K (fun v => a0 + nD * f v + Gd * g v) ≤
      2 * a0 + nD * Formalism.PairingDivisionLocalBalance.meanInf K f + Gd * Formalism.PairingDivisionLocalBalance.meanInf K g := by
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hc : (Fintype.card (InfinitePlace K) : ℝ) ≤ Module.finrank ℚ K := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
    exact_mod_cast (by omega : Fintype.card (InfinitePlace K) ≤ Module.finrank ℚ K)
  have h3 : 2 / (Module.finrank ℚ K : ℝ) * ((Fintype.card (InfinitePlace K) : ℝ) * a0) ≤ 2 * a0 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hn]
    nlinarith
  nlinarith [h3]

theorem exists_avg {α : Type} (S : Set α) (hS : S.Finite) (hne : S.Nonempty) (a0 nD Gd : ℝ) (h1 h2 : α → ℝ) :
    (∃ ρ ∈ S, a0 + nD * h1 ρ + Gd * h2 ρ ≤
      a0 + nD * ((∑ᶠ ρ ∈ S, h1 ρ) / Nat.card S) + Gd * ((∑ᶠ ρ ∈ S, h2 ρ) / Nat.card S)) ∧
    (∃ ρ ∈ S, a0 + nD * ((∑ᶠ ρ ∈ S, h1 ρ) / Nat.card S) + Gd * ((∑ᶠ ρ ∈ S, h2 ρ) / Nat.card S) ≤
      a0 + nD * h1 ρ + Gd * h2 ρ) := by
  set s := hS.toFinset with hs
  have hsne : s.Nonempty := by rwa [hs, Set.Finite.toFinset_nonempty]
  have hcard : (Nat.card S : ℝ) = s.card := by
    rw [hs, Nat.card_eq_card_finite_toFinset hS]
  have hs1 : ∑ᶠ ρ ∈ S, h1 ρ = ∑ ρ ∈ s, h1 ρ := finsum_mem_eq_finite_toFinset_sum _ hS
  have hs2 : ∑ᶠ ρ ∈ S, h2 ρ = ∑ ρ ∈ s, h2 ρ := finsum_mem_eq_finite_toFinset_sum _ hS
  have hc0 : (0 : ℝ) < s.card := by exact_mod_cast hsne.card_pos
  set m := a0 + nD * ((∑ᶠ ρ ∈ S, h1 ρ) / Nat.card S) + Gd * ((∑ᶠ ρ ∈ S, h2 ρ) / Nat.card S) with hm
  have key : ∑ ρ ∈ s, (a0 + nD * h1 ρ + Gd * h2 ρ) = ∑ _ρ ∈ s, m := by
    rw [Finset.sum_const, nsmul_eq_mul, hm, hs1, hs2, hcard, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    field_simp
  constructor
  · obtain ⟨ρ, hρ, h⟩ := Finset.exists_le_of_sum_le hsne key.le
    exact ⟨ρ, by rwa [hs, Set.Finite.mem_toFinset] at hρ, h⟩
  · obtain ⟨ρ, hρ, h⟩ := Finset.exists_le_of_sum_le hsne key.ge
    exact ⟨ρ, by rwa [hs, Set.Finite.mem_toFinset] at hρ, h⟩

theorem infTopK : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → InfTopK := by
  intro hP hI hD hDp
  obtain ⟨C1, hC1, hmean⟩ := GlobalTheory.T.exists_const_mean_logArea_logThetaNorm_le
  obtain ⟨CF0, hCF⟩ := GlobalTheory.T.conjugate_top_bound_of_inputs hP hI hD hDp C1 hC1
  obtain ⟨CF0', hCF'⟩ := GlobalTheory.T.rationalEqualSignKernels_largeConstants
  refine ⟨max CF0 CF0', fun CF hCF0 => ?_⟩
  obtain ⟨C0, hC0⟩ := hCF CF (le_trans (le_max_left _ _) hCF0)
  obtain ⟨C0', hC0'⟩ := hCF' CF (le_trans (le_max_right _ _) hCF0)
  refine ⟨max C0 C0', fun ε C hC => ?_⟩
  obtain ⟨x0, hx0⟩ := hC0 ε C (le_trans (le_max_left _ _) hC)
  obtain ⟨x0', hx0'⟩ := hC0' ε C (le_trans (le_max_right _ _) hC)
  refine ⟨max x0 x0', fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hF => ?_⟩
  obtain ⟨a0, nD, Gd, ha0, hnD, hGd, hsum, hbound⟩ :=
    hx0 D large₂ hε (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF
  have hrat := hx0' D large₂ hε (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF
  obtain ⟨hL1, hLrd, hLd⟩ := sizes D large₂ Γ Pl0 T A Ks R F hS
  obtain ⟨hmA, hmT⟩ := hmean D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 _ hL1 hLrd hLd
  refine ⟨fun p => a0 + nD * avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hArea D ch.S.Z.δ ch.S.Z.t0) +
    Gd * avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hTh D ch.S.Z.δ ch.S.Z.t0), ?_, ?_⟩
  · refine (meanInf_affine _ a0 nD Gd _ _ ha0).trans (le_trans ?_ hsum)
    have e1 := mul_le_mul_of_nonneg_left hmA hnD
    have e2 := mul_le_mul_of_nonneg_left hmT hGd
    nlinarith
  · intro p Φ β d hocc c j B v hv
    obtain ⟨f, hf⟩ := hrat Φ β d hocc c j
    obtain ⟨u, rfl, hu⟩ := hv
    refine ⟨f u, (hf u).symm, ?_⟩
    obtain ⟨hfin, hne⟩ := GlobalTheory.T.embeddingsCurveFieldAbove_finite_nonempty D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 p.embedding
    obtain ⟨⟨ρ₁, hρ₁, h₁⟩, ⟨ρ₂, hρ₂, h₂⟩⟩ := exists_avg _ hfin hne a0 nD Gd
      (hArea D ch.S.Z.δ ch.S.Z.t0) (hTh D ch.S.Z.δ ch.S.Z.t0)
    rcases le_or_gt 0 B with hB | hB
    · exact (hbound Φ β d hocc c j f hf p.embedding ρ₁ hρ₁ u B hu).trans
        (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h₁) hB)
    · exact (hbound Φ β d hocc c j f hf p.embedding ρ₂ hρ₂ u B hu).trans
        (mul_le_mul_of_nonpos_right (Real.exp_le_exp.2 h₂) hB.le)

end GlobalTheory.KerConjMean
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemilocalMirabolicWhittaker
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory.JSW.MirSemi

theorem kirillov_semilocal : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart b g) (invSet E (m + 1))) → ∀ (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit φ.1 p ≠ 0) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∀ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit F p = b p) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ k : GA E (m + 1), GeneralLinearGroup.map (pInf E) k = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) k = 1) → (∀ g, φ.1 (g * k) = φ.1 g) → ∀ g, F (g * k) = F g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  intro E _ _ _ m S b hbe hbC hbU hbs π φ hφ hnz
  obtain ⟨𝒲, hw0, h1, h2, h3, h4, h5, hback⟩ := GlobalTheory.T.exists_cusp_form_semi_local_whittaker_space E m S π φ hφ
  obtain ⟨W, hW, hWb⟩ := GlobalTheory.T.kirillov_semiLocal_mirabolic_abstract E m S b hbe hbC hbU hbs 𝒲 h1 h2 h3 h4 h5 ⟨_, hw0, hnz⟩
  obtain ⟨F, hF, hFW⟩ := hback W hW
  exact ⟨F, locSpan_le_mspanR hφ hF, fun p hp => by rw [hFW, hWb p hp],
    GlobalTheory.T.archimedeanKernelSpan_cuspForm_right_invariant_open E (m + 1) S π φ hφ F hF, fun k hk1 hk2 hk3 => GlobalTheory.T.semiLocalSpan_rightInvariant_of_trivial_infinity_finset E (m + 1) S φ.1 k hk1 hk2 hk3 F hF,
    fun t c ht1 ht2 ht3 => GlobalTheory.T.whittaker_relation_passes_to_semi_local_span E (m + 1) S π φ hφ t c ht1 ht2 ht3 F hF⟩

end GlobalTheory.JSW.MirSemi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarModelLocalTripleStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_bar_model_local_triple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (f : AE F E), GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl (incM F G.V'.J)),
      ((w : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (AE F E))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    ∀ S : (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) → ℂ) →
        ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) → ℂ,
    (∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      S Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v)) →
    (∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      ∀ Φ' ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), ∀ c : ℂ, S (c • Φ + Φ') = c • S Φ + S Φ') →
    (∀ u, At (evFin F v) u → ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) =
        schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (actB (cA σ) w u)) (S Φ)) →
    ∃ c : ℂ, ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      GlobalTheory.SwapSlice.sliceT ι (S Φ) = c • (GlobalTheory.SwapSlice.sliceT ι Φ ∘ GlobalTheory.SwapSlice.swapNeg) := by
  first | exact @GlobalTheory.SwapSchur.sliceT_swap_eq_smul | exact GlobalTheory.SwapSchur.sliceT_swap_eq_smul | (intros; apply GlobalTheory.SwapSchur.sliceT_swap_eq_smul <;> assumption)
end

