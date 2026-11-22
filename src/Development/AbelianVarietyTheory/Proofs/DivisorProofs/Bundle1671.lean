import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1630
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1553
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0253
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0702
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0794
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0730
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0793
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0723
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0115
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0114
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0057
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitive
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1642
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataCountableRank
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.PolRank

open Module

theorem rank_tens_le (F : Type) [Field F] [NumberField F] (P Q R S : ℕ) :
    Module.rank ℂ (GlobalTheory.RealLift.Tens F P Q R S) ≤ Cardinal.aleph0 := by
  classical
  let b := Basis.piTensorProduct (fun _ : InfinitePlace F =>
    (MvPolynomial.basisMonomials _ ℂ : Basis _ ℂ (Formalism.BasicNotions.TH.Pol P Q R S)))
  have hb := b.mk_eq_rank
  rw [Cardinal.lift_id, Cardinal.lift_id] at hb
  rw [← hb]
  exact Cardinal.mk_le_aleph0

theorem incM_map_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m : ℕ}
    (J : Matrix (Fin m) (Fin m) E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, inclR, compInf, infEmb_tmul]

theorem rank_pol_le : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → Module.rank ℂ (M.Pol B.ψ B.emb) ≤ Cardinal.aleph0 := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' h
  have hX := fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists n r s _ (X.θ w) (h.herm.sig w) (h.herm.cartan w)
  have hW := fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists d r' s' _ (W.θ w) (h.skew.sig w) (h.skew.cartan w)
  choose A hA hAθ using hX
  choose C hC hCθ using hW
  have hfr : GlobalTheory.RealLift.Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := by
    refine ⟨one_mul _, fun w => ?_, fun w => ?_⟩
    · rw [incM_map_piInf, one_smul]; exact hA w
    · rw [incM_map_piInf]; exact hC w
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) r s r' s' B.ψ B.emb
    (incM F X.J) (incM F W.J) M.co 1 Complex.I A C h.base.cm h.base.std hfr
  have hr := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.T.archActionReadings_compatible GlobalTheory.T.archHeisenbergDerivatives_exist (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives GlobalTheory.T.archHeisenbergDerivatives_exist) F E σ n d r s r' s' X W M B.ψ B.emb
    A C Φ h.base.cm h.base.std hfr hAθ hCθ hΦ
  rw [← hr]
  exact (rank_range_le Φ).trans (rank_tens_le F r s r' s')

end GlobalTheory.ThK.PolRank

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.TopForm GlobalTheory.Adelic GlobalTheory.TangentOrigin
open GlobalTheory.FlagTan (IsDef)

theorem exists_isFreeGen_dForm {k A : Type} [CommRing k] [CommRing A] {α : k →+* A} {D : ℕ}
    (h : α.IsStandardSmoothOfRelativeDimension D) : ∃ f : Fin D → A, IsFreeGen A (dForm α f) := by
  classical
  letI := α.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D k A := h
  obtain ⟨ι, σ, _, _, P, hP⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension D k A›.out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = D := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]
    simp [Algebra.Presentation.dimension]
  let e := Fintype.equivFinOfCardEq hc
  exact ⟨fun i => P.val (e.symm i), isFreeGen_dForm _ (P.basisKaehler.reindex e) fun i => by
    simp⟩

theorem exists_isFrame_dOn {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (D : ℕ)
    [SmoothOfRelativeDimension D p] (x : Y) :
    ∃ (U : Y.Opens) (f : Fin D → Γ(Y, U)), x ∈ U ∧ IsFrame (dOn p f) := by
  obtain ⟨V, hV, hx, -⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (Opens.mem_top x)
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(Y, V)), x ∈ Y.basicOpen (t : Γ(Y, V)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(Y, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, V))))
  have h₂ : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (Y.basicOpen (t : Γ(Y, V)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← resG_comp_algX p (Y.basicOpen_le (t : Γ(Y, V)))]
    exact h₁
  obtain ⟨f, hf⟩ := exists_isFreeGen_dForm h₂
  exact ⟨_, f, hxt, IsAffineOpen.basicOpen hV _, hf⟩

theorem primeSpectrum_dualNumber_eq {L : Type} [Field L] (x y : PrimeSpectrum (DualNumber L)) : x = y := by
  have h : ∀ z : PrimeSpectrum (DualNumber L), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
    constructor
    · intro ha
      by_contra h0
      exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
    · intro ha
      refine z.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
      exact z.asIdeal.zero_mem
  ext a
  rw [h, h]

theorem le_preimage_of_dualNumber {L : Type} [Field L] {T : Scheme.{0}} (φ : DualNumber L →+* L)
    (x : Sp (DualNumber L) ⟶ T) (V : T.Opens) (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  have hp : (spMap φ) (IsLocalRing.closedPoint L) = s := primeSpectrum_dualNumber_eq _ _
  have h₁ : (spMap φ ≫ x) (IsLocalRing.closedPoint L) ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}
  (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw))

theorem exists_tanLift {L : Type} [Field L] [Algebra c.F L] {Q : FrPt Xo c L} {v : FrPt Xo c (DualNumber L)}
    (hd : IsDef Q v) {z : Sp L ⟶ M.X} (hz : z ≫ toFlag M = X.ptY Q) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) :
    ∃ zv : Sp (DualNumber L) ⟶ M.X, zv ≫ toFlag M = X.ptY v ∧ ∀ O : M.X.Opens, ⊤ ≤ z ⁻¹ᵁ O → ⊤ ≤ zv ⁻¹ᵁ O := by
  have e := (X.ptY_frMap hd).trans hz.symm
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hb : ⊤ ≤ X.ptY v ⁻¹ᵁ (inc₀ X Z).opensRange := le_preimage_of_dualNumber _ _ _ (by
    rw [e]
    rintro s -
    exact ⟨(z ≫ M.σ) s, rfl⟩)
  have hr : Set.range (X.ptY v) ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    exact hb (Set.mem_univ s)
  obtain ⟨w, hw⟩ : ∃ w, w ≫ inc₀ X Z = X.ptY v := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have ered : spMap (GlobalTheory.FlagTan.red c L).toRingHom ≫ w = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, hw, e, Category.assoc]
  have hwU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z := le_preimage_of_dualNumber _ _ _ (by rw [ered]; exact hU)
  obtain ⟨zv, hzv, -⟩ := M.existsUnique_lift w hwU
  have hred : spMap (GlobalTheory.FlagTan.red c L).toRingHom ≫ zv = z :=
    (M.existsUnique_lift (z ≫ M.σ) hU).unique (by rw [Category.assoc, hzv, ered]) rfl
  refine ⟨zv, ?_, fun O hO => le_preimage_of_dualNumber _ _ _ (by rw [hred]; exact hO)⟩
  rw [toFlag, ← Category.assoc, hzv, hw]

theorem IsKS.val_eq_of_ksIso
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y)
    {ω ω' : H0 M.str (LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)) M.off} (h : IsKS M ω) (h' : IsKS M ω')
    {L : Type} [Field L] (z : Sp L ⟶ M.X) (i : M.K.bundle.ι) (k : X.F.J) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    (hi : ⊤ ≤ z ⁻¹ᵁ (LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k)) :
    H0.val (B := LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)) z (i, flagIdx M _ k) ho hi ω =
      H0.val (B := LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)) z (i, flagIdx M _ k) ho hi ω' := by
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hF : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ flagOpen X := hU
  have hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k := fun s _ =>
    (((common₀ X Z).pull M.σ).mem _ _ _).1 (hi (Set.mem_univ s)).2
  obtain ⟨_, hch⟩ := exists_chartFr _ hF
  obtain ⟨Q, hQ⟩ := hch k hk
  have hb := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L).1 Q
  obtain ⟨v, hv⟩ := (hKS L Q).exists_isTanFrame
  have e : z ≫ toFlag M = X.ptY Q := GlobalTheory.FlagMod.FlagCover.eq_ptY hQ.lies
  choose zv hzv hzO using fun b => exists_tanLift M (hv.isDef b) e ho
  have hpi : ptOf z ∈ M.K.bundle.U i := ((le_iff_ptOf_mem z _).1 hi).1
  obtain ⟨V, f, hx, hf⟩ := exists_isFrame_dOn M.str (GlobalTheory.FlagTan.dimFlag Dw) (ptOf z)
  obtain ⟨O, hO, hxO, hOV⟩ := Opens.isBasis_iff_nbhd.1 M.X.isBasis_affineOpens (show ptOf z ∈ V ⊓ M.K.bundle.U i from ⟨hx, hpi⟩)
  have hOV' : O ≤ V := hOV.trans inf_le_left
  have hOi : O ≤ M.K.bundle.U i := hOV.trans inf_le_right
  let g : Fin (GlobalTheory.FlagTan.dimFlag Dw) → Γ(M.X, O) := fun a => resG M.X hOV' (f a)
  have hu : IsUnit (M.K.jacobian i hOi g) := (M.K.isUnit_jacobian_iff i hO hOi g).2 (by
    have := hf.res hO hOV'
    rwa [resForm_dOn] at this)
  have hzO' : ⊤ ≤ z ⁻¹ᵁ O := (le_iff_ptOf_mem z _).2 hxO
  have a := h L Q Q 1 v z zv i k O hOi g hzO' (fun b => hzO b O hzO') hk ho hi hQ hb hv hzv
  have hd : (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzO _ O hzO') (g a)).snd).det ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at a
    exact mul_ne_zero (Units.ne_zero _) (hu.map (evalPt z O hzO')).ne_zero a.symm
  exact IsKS.val_eq M h h' hOi hzO' (hzv := fun b => hzO b O hzO') ho hi hQ hb hv hzv hd

theorem CanId.eq_of_ksIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ ω ω' : CanId M, ω = ω' := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS ω ω'
  haveI : Smooth M.str := SmoothOfRelativeDimension.smooth (GlobalTheory.FlagTan.dimFlag Dw) M.str
  haveI : IsReduced M.X := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isReduced_of_smooth M.str
  have e : ω.ω = ω'.ω := by
    refine H0.ext_germ fun y hy => ?_
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (X.F.cover.ge (Set.mem_univ (toFlag M y)))
    obtain ⟨i, hi⟩ := exists_chart M.K.isLB y
    have hm : y ∈ ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ).U (flagIdx M _ k) := (((common₀ X Z).pull M.σ).mem _ _ _).2 hk
    refine ⟨(i, flagIdx M _ k), ⟨hi, hm⟩, ?_⟩
    change ger y _ (H0.loc ω.ω _) = ger y _ (H0.loc ω'.ω _)
    refine congrArg _ (GlobalTheory.FlagMod.ext_ev_field fun L _ z hz => ?_)
    exact IsKS.val_eq_of_ksIso M hKS ω.isKS ω'.isKS z i k (GlobalTheory.FlagMod.le_preimage_mono inf_le_left hz)
      (GlobalTheory.FlagMod.le_preimage_mono inf_le_right hz)
  cases ω
  cases ω'
  cases e
  rfl

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceFixedVectorsNeBotTransportStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruence_fixedVectors_ne_bot_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (x : IrrGL k) (x' : IrrGL k'), RepRel i x x' → GlobalTheory.PRep.fixed x.rep (GlobalTheory.SplitWeil.KOne k (Fin x.1)) ≠ ⊥ → GlobalTheory.PRep.fixed x'.rep (GlobalTheory.SplitWeil.KOne k' (Fin x'.1)) ≠ ⊥ := by
  first | (exact @GlobalTheory.KOneTransport.fixed_ne_bot_transport) | (exact GlobalTheory.KOneTransport.fixed_ne_bot_transport) | (intros; apply GlobalTheory.KOneTransport.fixed_ne_bot_transport  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineChartFamiliesAgreeOnOverlapStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LineConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveLine_chart_families_agree_on_overlap : ∀ {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f₀ f₁ : Sp (Polynomial k) ⟶ B.left) (h0 : f₀ ≫ B.hom = spMap (algebraMap k (Polynomial k))) (h1 : f₁ ≫ B.hom = spMap (algebraMap k (Polynomial k))), spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) : Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁ → ∀ (R : Type) [CommRing R] [Algebra k R] (u v : R), u * v = 1 → spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ famMap B f₀ h0 R u = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) : Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ famMap B f₁ h1 R v := by
  first | exact @GlobalTheory.LineConst.famMap_loc_eq | exact GlobalTheory.LineConst.famMap_loc_eq | (intros; apply GlobalTheory.LineConst.famMap_loc_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveMapUniqueOfRelation
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.LineQuot

theorem isUnit_pullRatio_of_frame {k : Type} [CommRing k] {N : ℕ} {T : Scheme.{0}} {L Q : T.Modules}
    {s : Fin (N + 1) → (L ⟶ Q)} {χ : T ⟶ PSpace k N} (hχ : Rel χ s) {V : T.Opens} {i j : Fin (N + 1)}
    (hi : V ≤ χ ⁻¹ᵁ ProjSpace.chart k N i) (hb : Function.Bijective ((s j).app V))
    {e : Fin 1 → Γ(Q, V)} (he : IsFrame e) : IsUnit (ProjSpace.pullRatio χ V i hi j) := by
  set b := he.basis (le_refl V)
  obtain ⟨t, ht⟩ := hb.2 (b 0)
  set c := b.repr ((s i).app V t) 0
  have hc : (s i).app V t = c • b 0 := by
    conv_lhs => rw [← b.sum_repr ((s i).app V t)]
    simp [Fin.sum_univ_one, c]
  have h1 := hχ i j V hi t
  rw [ht, hc, smul_smul] at h1
  have h2 := congrArg (fun x => b.repr x 0) h1
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
    mul_one] at h2
  exact .of_mul_eq_one _ h2.symm

theorem pullRatio_smul_eq {k : Type} [CommRing k] {N : ℕ} {T : Scheme.{0}} {L Q : T.Modules}
    {s : Fin (N + 1) → (L ⟶ Q)} {χ : T ⟶ PSpace k N} (hχ : Rel χ s) {V : T.Opens} {j : Fin (N + 1)}
    (hj : V ≤ χ ⁻¹ᵁ ProjSpace.chart k N j) (t : Γ(L, V)) (m : Fin (N + 1)) :
    (s m).app V t = ProjSpace.pullRatio χ V j hj m • (s j).app V t :=
  hχ j m V hj t

theorem le_preimage_chart {k : Type} [CommRing k] {N : ℕ} {T : Scheme.{0}} {L Q : T.Modules}
    {s : Fin (N + 1) → (L ⟶ Q)} {χ : T ⟶ PSpace k N} (hχ : Rel χ s) {V : T.Opens} {i j : Fin (N + 1)}
    (hi : V ≤ χ ⁻¹ᵁ ProjSpace.chart k N i) (hb : Function.Bijective ((s j).app V))
    {e : Fin 1 → Γ(Q, V)} (he : IsFrame e) : V ≤ χ ⁻¹ᵁ ProjSpace.chart k N j := by
  have h := ProjSpace.basicOpen_pullRatio (φ := χ) (W := V) (i := i) (hi := hi) (j := j)
  rw [T.basicOpen_of_isUnit (isUnit_pullRatio_of_frame hχ hi hb he)] at h
  exact h.le.trans inf_le_right

theorem exists_mem_preimage_chart {k : Type} [CommRing k] {N : ℕ} {T : Scheme.{0}} (χ : T ⟶ PSpace k N)
    (y : T) : ∃ i, y ∈ χ ⁻¹ᵁ ProjSpace.chart k N i := by
  have : χ y ∈ (⨆ i, ProjSpace.chart k N i : (PSpace k N).Opens) := by
    rw [ProjSpace.iSup_chart]; trivial
  exact (TopologicalSpace.Opens.mem_iSup (s := fun i => ProjSpace.chart k N i)).1 this

theorem eq_of_rel : ∀ (k : Type) [CommRing k] (N : ℕ) (T : Scheme.{0}) (L Q : T.Modules)
    (s : Fin (N + 1) → (L ⟶ Q)) (φ ψ : T ⟶ PSpace k N), IsVB L 1 → IsVB Q 1 → Gen s →
    φ ≫ PSpace.str k N = ψ ≫ PSpace.str k N → Rel φ s → Rel ψ s → φ = ψ := by
  intro k _ N T L Q s φ ψ _ hQ hG hstr hφ hψ
  refine ProjSpace.hom_ext hstr fun y => ?_
  obtain ⟨j, W, hyW, hbij⟩ := hG y
  obtain ⟨i, hi⟩ := exists_mem_preimage_chart φ y
  obtain ⟨l, hl⟩ := exists_mem_preimage_chart ψ y
  obtain ⟨V, e, -, hyV, hV, he⟩ := hQ.exists_affine
    (V := W ⊓ φ ⁻¹ᵁ ProjSpace.chart k N i ⊓ ψ ⁻¹ᵁ ProjSpace.chart k N l) ⟨⟨hyW, hi⟩, hl⟩
  have hb := hbij V (hV.trans (inf_le_left.trans inf_le_left))
  have hjφ := le_preimage_chart hφ (hV.trans (inf_le_left.trans inf_le_right)) hb he
  have hjψ := le_preimage_chart hψ (hV.trans inf_le_right) hb he
  refine ⟨V, hyV, j, hjφ, hjψ, fun m => ?_⟩
  set b := he.basis (le_refl V)
  obtain ⟨t, ht⟩ := hb.2 (b 0)
  have h := (pullRatio_smul_eq hφ hjφ t m).symm.trans (pullRatio_smul_eq hψ hjψ t m)
  rw [ht] at h
  have h2 := congrArg (fun x => b.repr x 0) h
  simpa only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
    mul_one] using h2

end GlobalTheory.LineQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveMapUniversalLine
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LineQuot

set_option backward.isDefEq.respectTransparency false in

theorem exists_taut_quot : ∀ (k : Type) [CommRing k] (N : ℕ) (T : Scheme.{0}) (φ : T ⟶ PSpace k N) (L : T.Modules), IsVB L 1 → ∃ (Q : T.Modules) (s : Fin (N + 1) → (L ⟶ Q)), IsVB Q 1 ∧ JointEpi s ∧ Rel φ s := by
  intro k _ N T φ L hL
  have hM : ((ProjSpace.O1 k N).pull φ).IsLB := LB.isLB_pull (ProjSpace.O1_isLB k N) φ
  refine ⟨twist L ((ProjSpace.O1 k N).pull φ),
    fun j => Twist.secHom L (Cartier.secPull (ProjSpace.coord k N j) φ), hL.twist hM, ?_, ?_⟩
  · intro Z a ha
    have hc := ProjSpace.iSup_nonzeroLocus_secPull (ProjSpace.iSup_nonzeroLocus_coord k N) φ
    ext V q
    refine Twist.sec_ext_of_cover
      (fun j => V ⊓ Out.nonzeroLocus (Cartier.secPull (ProjSpace.coord k N j) φ)) (fun _ => inf_le_left)
      (GlobalTheory.LB.le_iSup_inf hc V) fun j => ?_
    rw [← Twist.app_resM, ← Twist.app_resM]
    obtain ⟨t, ht⟩ := (Twist.bijective_secHom_app (F := L) hM (Cartier.secPull (ProjSpace.coord k N j) φ)
      (V := V ⊓ Out.nonzeroLocus (Cartier.secPull (ProjSpace.coord k N j) φ)) inf_le_right).2
      (Twist.resM _ inf_le_left q)
    rw [← ht]
    have e := congrArg (fun m => (Scheme.Modules.Hom.app m (V ⊓ Out.nonzeroLocus (Cartier.secPull (ProjSpace.coord k N j) φ))) t) (ha j)
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at e
    rw [e]
    simp
  · intro i j W h t
    have hW : W ≤ ((ProjSpace.O1 k N).pull φ).U (fun _ => i) := h.trans (Cartier.pull_U (ProjSpace.O1 k N) φ fun _ => i).ge
    apply (Twist.chartEquiv hM (fun _ => i) hW).injective
    rw [LinearEquiv.map_smul, Twist.chartEquiv_secHom_app, Twist.chartEquiv_secHom_app,
      ProjSpace.resG_secPull_coord, ProjSpace.resG_secPull_coord, ProjSpace.pullRatio_self, one_smul]

end GlobalTheory.LineQuot

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveRelationPullback
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot

set_option autoImplicit false

noncomputable section

open GlobalTheory.Twist (resM resM_resM resM_smul app_resM sec_ext_of_cover)

namespace GlobalTheory.LineQuot

theorem rel_pullback : ∀ (k : Type) [CommRing k] (N : ℕ) (S T : Scheme.{0}) (g : S ⟶ T) (L Q : T.Modules)
    (s : Fin (N + 1) → (L ⟶ Q)) (φ : T ⟶ PSpace k N), IsVB L 1 → IsVB Q 1 → Rel φ s →
    Rel (g ≫ φ) fun j => (Scheme.Modules.pullback g).map (s j) := by
  intro k _ N S T g L Q s φ hL _ hs i j W hW t
  haveI := hL.isQuasicoherent
  beta_reduce
  set A := (Scheme.Modules.pullback g).map (s j)
  set B := (Scheme.Modules.pullback g).map (s i)

  have hsmul : ∀ (U : S.Opens) (hU : U ≤ (g ≫ φ) ⁻¹ᵁ ProjSpace.chart k N i) (c : Γ(S, U))
      (u : Γ((Scheme.Modules.pullback g).obj L, U)),
      A.app U u = ProjSpace.pullRatio (g ≫ φ) U i hU j • B.app U u →
      A.app U (c • u) = ProjSpace.pullRatio (g ≫ φ) U i hU j • B.app U (c • u) := by
    intro U hU c u h
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, h, smul_smul, smul_smul, mul_comm]
  have hW' : W ≤ g ⁻¹ᵁ (φ ⁻¹ᵁ ProjSpace.chart k N i) := hW
  have loc : ∀ y : W, ∃ (V : T.Opens) (e : Fin 1 → Γ(L, V)), (y : S) ∈ g ⁻¹ᵁ V ∧ V ≤ φ ⁻¹ᵁ ProjSpace.chart k N i ∧
      IsFrame e := fun y => by
    obtain ⟨V, e, -, hy, hV, he⟩ := hL.exists_affine (x := g y) (V := φ ⁻¹ᵁ ProjSpace.chart k N i) (hW' y.2)
    exact ⟨V, e, hy, hV, he⟩
  choose V e hy hV he using loc
  refine sec_ext_of_cover (fun y => W ⊓ g ⁻¹ᵁ V y) (fun _ => inf_le_left)
    (fun y hyW => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hyW⟩, hyW, hy _⟩) fun y => ?_
  have hU : W ⊓ g ⁻¹ᵁ V y ≤ (g ≫ φ) ⁻¹ᵁ ProjSpace.chart k N i := inf_le_left.trans hW
  have hgV : g ⁻¹ᵁ V y ≤ (g ≫ φ) ⁻¹ᵁ ProjSpace.chart k N i := g.preimage_mono (hV y)

  have hpb : A.app (g ⁻¹ᵁ V y) (QCoh.pullbackSections g L (le_refl _) (e y 0)) =
      ProjSpace.pullRatio (g ≫ φ) (g ⁻¹ᵁ V y) i hgV j • B.app (g ⁻¹ᵁ V y) (QCoh.pullbackSections g L (le_refl _) (e y 0)) := by
    rw [QCoh.pullback_map_app_pullbackSections, QCoh.pullback_map_app_pullbackSections,
      hs i j (V y) (hV y) (e y 0), QCoh.pullbackSections_smul, ProjSpace.appLE_pullRatio]
  have hres : A.app (W ⊓ g ⁻¹ᵁ V y) (resM _ inf_le_right (QCoh.pullbackSections g L (le_refl _) (e y 0))) =
      ProjSpace.pullRatio (g ≫ φ) (W ⊓ g ⁻¹ᵁ V y) i hU j •
        B.app (W ⊓ g ⁻¹ᵁ V y) (resM _ inf_le_right (QCoh.pullbackSections g L (le_refl _) (e y 0))) := by
    rw [app_resM, app_resM, hpb, resM_smul, ProjSpace.resG_pullRatio]
  obtain ⟨a, ha⟩ := ((he y).pullback g (W ⊓ g ⁻¹ᵁ V y) inf_le_right).2 (resM _ inf_le_left t)
  rw [Fintype.linearCombination_apply, Fin.sum_univ_one] at ha
  rw [← app_resM, resM_smul, ← app_resM, ProjSpace.resG_pullRatio, ← ha]
  exact hsmul _ _ _ _ hres

end GlobalTheory.LineQuot

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullActLev
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

open CategoryTheory

namespace GlobalTheory.LevPullEquiv

set_option maxHeartbeats 1000000 in

theorem pull_actLev : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → (∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) → ∀ (G G₂ : Type) [Group G] [Group G₂] (lev : G → Dw.La →ₗ[𝓞 D.host.E] Dw.La) (lev₂ : G₂ → Dw.La →ₗ[𝓞 D.host.E] Dw.La), ActLev (Xo := Xo) c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) → ActLev (Xo := d.Xo₂) d.c₂ (fun g => (lev₂ g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) → ∀ (g : G) (g₂ : G₂), CongMod l.Mb (lev₂ g₂) (lev g) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ f₂ ∈ sec d.Xo₂ d.c₂ a n, Pull d f f₂ → Pull d (actLev c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) g f) (actLev d.c₂ (fun g => (lev₂ g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) g₂ f₂) := by
  intro D j H Dw l Xo c d hpq hlev hA2 hbase G G₂ _ _ lev lev₂ hact hact₂ g g₂ hcong a n f hf f₂ hf₂ hpull
  intro k _ _ _ _ hk y₂ y hov
  have e1 : evR Xo c (actLev c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) g f) y =
      evR Xo c f (mvPt _ _ g y) :=
    evalAt_actL hact (GlobalTheory.TransferCompare.evalWD_framed _ _) frMap_trans_id g hf.1 y
  have e2 : evR d.Xo₂ d.c₂ (actLev d.c₂ (fun g => (lev₂ g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) g₂ f₂) y₂ =
      evR d.Xo₂ d.c₂ f₂ (mvPt _ _ g₂ y₂) :=
    evalAt_actL hact₂ (GlobalTheory.TransferCompare.evalWD_framed _ _) frMap_trans_id g₂ hf₂.1 y₂
  rw [e1, e2]
  obtain ⟨ρ, ν, hi, hmv, hfm⟩ := mvPt_spec hact.total g y
  obtain ⟨ρ₂, ν₂, hi₂, hmv₂, hfm₂⟩ := mvPt_spec hact₂.total g₂ y₂
  obtain ⟨hd, hM, -, -, -, hE, hlift, -, -⟩ := id hlev
  obtain ⟨r', m', hsq₁, hsq₂, hE'⟩ := GlobalTheory.exists_conj_levelMap D.host.E H Dw l Xo c 0 d hE ρ ν (asIso ρ₂) ν₂
    (lev g) LinearMap.id (lev₂ g₂) LinearMap.id hmv hmv₂ hcong (fun x => ⟨0, by simp⟩)
  have hov' := GlobalTheory.frOver_of_square_of_frMove D.host.E H Dw l Xo c 0 d ρ ν ρ₂ ν₂ r' m' hsq₁ hsq₂ k y _ y₂ _ hov hfm hfm₂
  obtain ⟨z₂, hz₂⟩ := hlift k hk _
  have hL : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.T.abelianScheme_laws_unconditional.1
  have hN := GlobalTheory.levelMaps_closed hL D.host.E H Dw hpq
  obtain ⟨g', ρ', ν', hg', -, hmv', hfm'⟩ :=
    GlobalTheory.exists_levMove_of_frOver hL D.host.E H Dw l Xo c 0 d hN hd hM hE r' m' hE' k hk _ z₂ _ hz₂ hov'
  obtain ⟨e₁, e₂⟩ := GlobalTheory.levMove_comm_levelMap_of_trivial_mod D.host.E H Dw l Xo c 0 d hpq hlev hA2 hbase ρ'.hom ν'
    (g'.f d.l₂.M) (g'.f d.l₂.A) inferInstance hmv' (fun x => GlobalTheory.LevelFibre.sub_mem_of_inGam hd hg' x)
  obtain ⟨⟨ι, hι, hone⟩, -, -⟩ := GlobalTheory.T.framedPointMove_calculus D.host.E H Dw l Xo c
  have hfin := GlobalTheory.frOver_of_square_of_frMove D.host.E H Dw l Xo c 0 d (𝟙 _) ι ρ'.hom ν' d.r d.m
    (by rw [e₁, Category.comp_id]) (by rw [e₂, hι, Category.comp_id]) k _ _ z₂ _ hz₂ (hone k _) hfm'
  exact hpull k hk _ _ hfin

end GlobalTheory.LevPullEquiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLineBundleSectionsLeImageFormsStatement
section
open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankGrowth_lineBundle_sections_le_image_forms : ∀ (k : Type) [Field k] [CharZero k] (S : LinSys k), S.IsVariety → S.BasePointFree → S.Birational → growth S.D (fun m => (lbH0 k (lbPow S.L m) : ℕ∞)) ≤ growth S.D (fun m => (Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) := by
  first | exact @GlobalTheory.SecGrowth.rankGrowth_lineBundleSections_le_image_forms | exact GlobalTheory.SecGrowth.rankGrowth_lineBundleSections_le_image_forms | (intros; apply GlobalTheory.SecGrowth.rankGrowth_lineBundleSections_le_image_forms <;> assumption)
end

