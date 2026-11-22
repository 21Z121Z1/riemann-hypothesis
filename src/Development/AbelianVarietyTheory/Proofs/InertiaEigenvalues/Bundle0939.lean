import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFirstOfSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0107
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0251
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0933
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0916
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotNonemptyZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0792
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0936
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0935

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormalisedDataNormalCoefficientField
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.PinsNormal

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levJ_eq (R : RealDat D A Ks) (i : Fin D.R.m) {t t' : T0} (e : R.Q t' = R.Q t) : levJ R i t' = levJ R i t := by
  have key : ∀ (Q Q' : Finset (Pl D.host.E)) (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), Q = Q' →
      lev D.sp.cm (Vc D i).gram (R.βV i) (Lev.flag1L (Lev.datY _ D.R.r D.R.t 1 (r_le_V i) R.Pg Q (LevelP.triv _ _ _)
        (fun _ => R.chi ((i : ℕ) + 1)) ξ Lev.Frm.A)) =
      lev D.sp.cm (Vc D i).gram (R.βV i) (Lev.flag1L (Lev.datY _ D.R.r D.R.t 1 (r_le_V i) R.Pg Q' (LevelP.triv _ _ _)
        (fun _ => R.chi ((i : ℕ) + 1)) ξ' Lev.Frm.A)) := by
    rintro Q _ ξ ξ' rfl
    exact Subgroup.ext fun x => Iff.rfl
  have h := key _ _ (R.xiR t') (R.xiR t) e
  unfold levJ levEnv
  exact congrArg (fun K => (Lev.toAfE (Vc D i) K).comap (finHom (Vc D i)).range.subtype) h

theorem repsR_of_eq (R : RealDat D A Ks) (i : Fin D.R.m) {t t' : T0} (e : R.Q t' = R.Q t) {K' : Type} [Field K'] {Cl : Type} [Fintype Cl]
    {h : Cl → GA D (Vc D i)} {bad : ℕ} {J' : Subgroup (Bridge.Gf (Vc D i))}
    {Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)} {gam : Cl → ℕ} {vol : K'}
    (H : RepsR R i t' h bad J' Lh gam vol) : RepsR R i t h bad J' Lh gam vol := by
  unfold RepsR at H ⊢
  rwa [levJ_eq R i e, e] at H

theorem extC_down (R : RealDat D A Ks) (i : Fin D.R.m) {K₁ K₂ : Type} [Field K₁] [Field K₂] (j₁ : D.what₂.LL →+* K₁) (j₂ : D.what₂.LL →+* K₂)
    (σ₁ : K₁ →+* ℂ) (σ₂ : K₂ →+* ℂ) (h₁ : σ₁.comp j₁ = D.what₂.embLL) (h₂ : σ₂.comp j₂ = D.what₂.embLL)
    (hs : Function.Surjective j₁) (c0 : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W)
    (a₁ : VsV D i K₁ →ₛₗ[σ₁] (R.cV i).W) (a₂ : VsV D i K₂ →ₛₗ[σ₂] (R.cV i).W)
    (H₁ : CoefficientBaseChange R i j₁ σ₁ c0 a₁) (H₂ : CoefficientBaseChange R i j₂ σ₂ c0 a₂) (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W)
    (hc : ExtC R i σ₂ a₂ c) : ExtC R i σ₁ a₁ c := by
  intro v v' e
  let ε : K₁ ≃+* D.what₂.LL := (RingEquiv.ofBijective j₁ ⟨j₁.injective, hs⟩).symm
  have hε : j₁.comp (ε : K₁ →+* D.what₂.LL) = RingHom.id K₁ := RingHom.ext fun x => (RingEquiv.ofBijective j₁ ⟨j₁.injective, hs⟩).apply_symm_apply x
  let u : VsV D i D.what₂.LL := ⟨MvPolynomial.map (ε : K₁ →+* D.what₂.LL) (v : Pol K₁ D.what₂.Tau (Vc D i).rank),
    Formalism.L2.Ker.map_mem_VV _ _ _ v.2⟩
  obtain ⟨w₁, e₁, f₁⟩ := H₁ u
  obtain ⟨w₂, e₂, f₂⟩ := H₂ u
  have hw : w₁ = v := Subtype.ext (by
    rw [e₁]
    change MvPolynomial.map j₁ (MvPolynomial.map (ε : K₁ →+* D.what₂.LL) (v : Pol K₁ D.what₂.Tau (Vc D i).rank)) = _
    rw [MvPolynomial.map_map, hε, MvPolynomial.map_id])
  rw [← hw, f₁, ← f₂]
  refine hc w₂ v' ?_
  rw [e, e₂, MvPolynomial.map_map, h₂, ← hw, e₁, MvPolynomial.map_map, h₁]

theorem exists_normal_coeff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    ∃ c' : Coeff l, c.F ≤ c'.F ∧ Normal ℚ c'.F := by
  have := c.fin
  have hle : c.F ≤ IntermediateField.normalClosure ℚ c.F ℂ := IntermediateField.le_normalClosure c.F
  have : IsNormalClosure ℚ c.F (IntermediateField.normalClosure ℚ c.F ℂ) :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure fun x => IsAlgClosed.splits _
  exact ⟨⟨IntermediateField.normalClosure ℚ c.F ℂ, inferInstance, fun τ a => hle (c.conj τ a), hle c.zeta_mem,
    c.le.trans hle⟩, hle, IsNormalClosure.normal (F := ℚ) (K := c.F) (L := IntermediateField.normalClosure ℚ c.F ℂ)⟩

set_option maxHeartbeats 4000000 in

theorem exists_pins_normal : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → ∃ M : OMDat T.toCore R i T0 id, M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) ∧ M.lev = (O i).lev ∧ (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) ∧ Normal ℚ M.c'.F ∧ GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 ∧ (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ M.c'.F) ∧ ∀ t t' : T0, R.Q t' = R.Q t → ∃ e, SameCover M t t' e := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O hC hfin hfw hG i hO
  obtain ⟨fw⟩ := id hfw
  have hT := fw.laws
  have hL : R.toLevCh.Is A.μ0 := hC.lev
  have hchi : R.grp_chiW := hC.grp.chiW
  have hfam := hC.fam
  have hmodels := hC.models
  have hvP : R.thP_vP := hC.thP.vP
  obtain ⟨hpb, hV, hlev⟩ := GlobalTheory.T.baseTuple_pins_orientation_standardFrame_levelMap D G Pl0 T0 A T R κ v₀ O hL hT i hO
  obtain ⟨gramR, c0R, c0L, htie, hc0O⟩ := hO.2.lift.c0
  haveI : Nonempty T0 := ⟨A.μ0⟩
  let rep : T0 → T0 := fun t => Function.invFun R.Q (R.Q t)
  have hrepQ : ∀ t, R.Q (rep t) = R.Q t := fun t => Function.invFun_eq (f := R.Q) ⟨t, rfl⟩
  have hrepE : ∀ t t' : T0, R.Q t' = R.Q t → rep t' = rep t := fun t t' e => congrArg (Function.invFun R.Q) e
  choose pd l₂ h1 h2 using GlobalTheory.CoverHalf.exists_half_of_laws T.toCore R hT.toLawsM hL hpb hG
  obtain ⟨c₁, hc1a, hc1b, hc1xi, hc⟩ := GlobalTheory.OneCover.exists_covers_rep T R hT hL i (Vc D i).rank pd
    (fun t => GlobalTheory.CoverHalf.coverHalf D (R.Q t)) l₂ h1 h2 rep hrepQ
  choose Mφ hMφ hφ using fun t => GlobalTheory.T.exists_level_place_datum_over_number_field D G Pl0 T0 A _ R hL hvP i hV t _ (iotaW T i)
    (GlobalTheory.PinnedDataGiven.latEmb_iotaW T hT i)
  choose MB hMB hB using fun t => GlobalTheory.T.exists_numberField_heckeCharacter_sqrtNorm_values D G Pl0 T0 A _ R hL i t
  have := c₁.fin
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.TupleCover.exists_coeff_ge T.Q.l (c₁.F ⊔ ⨆ t, (Mφ t ⊔ MB t))
  obtain ⟨c₃, hc₃, hcurve⟩ := GlobalTheory.CurveField.exists_coeff_curveOver _ T.Q.H T.Q.l c₂ 1 one_pos
  obtain ⟨c', hc', hnorm⟩ := exists_normal_coeff c₃
  have h23 : c₂.F ≤ c'.F := hc₃.trans hc'
  have h3 : c₁.F ≤ c'.F := (le_sup_left.trans hc₂).trans h23
  have h4 : ∀ t, Mφ t ⊔ MB t ≤ c'.F := fun t =>
    (((le_iSup (fun t => Mφ t ⊔ MB t) t).trans le_sup_right).trans hc₂).trans h23
  have hle : T.Q.c.F ≤ c'.F := hc1a.trans h3
  have hLL := hc1b.trans h3
  obtain ⟨d, U, dict, f, xi, -, hcov, hhalf, hxi, hcxi, hmod⟩ := hc c' hle h3
  let dδ : T0 → DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank := fun t => { d (rep t) with cδ := f t }
  let jL : D.what₂.LL →+* c'.F := D.what₂.embLL.codRestrict c'.F fun x => hLL ⟨x, rfl⟩
  have hjL : (inC c').comp jL = D.what₂.embLL := RingHom.ext fun _ => rfl
  obtain ⟨c0', hc0, hplace⟩ := GlobalTheory.T.exists_coefficientMap_extension_rational_values D G Pl0 T0 A _ R hL hchi hfam hmodels gramR c0R c0L htie i c'.F jL (inC c') hjL
  obtain ⟨Cl, fCl, h, J', bad, Lh, gam, vol, La, Nc, hrep, hbad, hcl⟩ :=
    GlobalTheory.SplitReps.exists_repsR_repsCov R i (hL.βV i) hV c'.F (T.Q.Xo ((i : ℕ) + 1)) c' id d
  have hrepR : ∀ t, RepsR R i t (h (rep t)) (bad (rep t)) (J' (rep t)) (Lh (rep t)) (gam (rep t)) (vol (rep t)) :=
    fun t => repsR_of_eq R i (hrepQ t) (hrep (rep t)).1
  choose B hBis using fun t => hB t c'.F (le_sup_right.trans (h4 t)) (bad (rep t)) (hbad (rep t)).2.2.2.2
    fun PP hPP => (hrepR t).2.1 PP (Or.inr hPP)
  have hodd : Odd ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q) := by
    obtain ⟨e1, e2, -⟩ := hT.pins.2.2.2 _ (inR i)
    have h5 := Formalism.L2.NTheta.odd_r D.R
    have h6 := i.2
    have h7 := D.R.m_add_three_le_k
    rw [e1, e2]
    convert h5 using 1
    simp only [Ranks.sigW, Ranks.r]
    omega
  choose epF hepF using fun t => (GlobalTheory.ClassTieCompare.exists_epIs_iff (n := (Vc D i).rank) (Dw := T.Q.Dw ((i : ℕ) + 1))
    (bad (rep t)) (B t)).2 fun L cc g d => GlobalTheory.T.law_of_squares_selfDual_splitLattice _ _ _ _ hodd L cc g.1 g.2.2 d.1 d.2
  obtain ⟨io, hw, hio⟩ := GlobalTheory.T.exists_harmonicCoefficientMap_at_weights D T.Q hT.pins κ fw.kap i c'
  choose φ hφis using fun t => hφ t c'.F (le_sup_left.trans (h4 t)) (hhalf t).2.2 (Mfr (dδ t).l₂) fun PP hPP c hc => by
    have hM : (dδ t).l₂.Mb ≤ PP.asIdeal := by
      rw [(hcov t).1.2.2.2.1]
      rcases hPP with hPP | hPP
      · rw [(hhalf t).1]
        exact Ideal.mul_le_left.trans (Ideal.prod_le_inf.trans (Finset.inf_le hPP))
      · exact Ideal.mul_le_right.trans ((hhalf t).2.1 PP hPP)
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ T.Q.H.bar.surjective).1 hc
    refine ⟨b, hM hb, ?_⟩
    change _ = star ((T.Q.H.bar b : 𝓞 D.host.E) : D.host.E)
    rw [T.Q.H.bar_eq]
    exact (star_star _).symm
  choose thAd hth using fun t => GlobalTheory.T.exists_adelicSide_of_models D G Pl0 T0 A _ R hmodels i t _ _ c0' _ (h (rep t)) _ (hrepR t).2.2.1
    (hrepR t).2.2.2.2.2.1 (v₀ i (sg0 D A))
  have hact := fun c => GlobalTheory.T.levelAction_framedPoints_isAction D G Pl0 T0 A T R hL hT hpb i c (O i).lev hlev
  let M : OMDat T.toCore R i T0 id :=
    { c' := c', hle := hle, jL := jL, hV := hT.spaceW _ (inR i) _ rfl, c0' := c0', lev := (O i).lev, dδ := dδ,
      Cl' := fun t => Cl (rep t), fCl := fun t => fCl (rep t),
      bad := fun t => bad (rep t), Lh := fun t => Lh (rep t), La := fun t => La (rep t), Nc := fun t => Nc (rep t),
      gam := fun t => gam (rep t), vol := fun t => vol (rep t), ep := fun t k => epF t (Lh (rep t) k), B := B,
      epF := epF, io := io, hw := hw, φ := φ,
      w := fun t _ q => (dδ t).eF.symm (phiHat (dδ t).c₂ (fun x => (dδ t).eF (φ t x)) q),
      U₂ := fun t => U (rep t), dict₂ := fun t => dict (rep t), xi := xi, thAd := thAd,
      Plc := fun t x => ∃ x₀, Place R i t (h (rep t)) c0' (jVx R i t x₀) x }
  have hMP : M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) :=
    ⟨⟨hjL, hV, fw.hv₀ i _, ⟨gramR, c0R, c0L, htie, hc0⟩, hlev⟩,
      fun t => ⟨⟨h (rep t), J' (rep t), hrepR t, hplace t _ _, hth t, fun _ => Iff.rfl⟩, hBis t, hxi t, hφis t, hhalf t⟩,
      ⟨hact _, hact _⟩, fun t => hbad (rep t), fun t => hcl (rep t), fun t => ⟨fun _ => rfl, hepF t⟩, hio,
      fun t k q => AlgEquiv.apply_symm_apply _ _, hcov, hcxi, hmod⟩
  refine ⟨M, hMP, rfl, ?_, hnorm, hcurve c' hc', fun t x => h3 (hc1xi t x), fun t t' e => ?_⟩
  · obtain ⟨cM, hcM, -, huM⟩ := GlobalTheory.T.coefficientMap_unique_bijective_complex_extension D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP
    obtain ⟨cO, -, -, huO⟩ := GlobalTheory.T.coefficientMap_unique_bijective_complex_extension D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i Unit (fun _ => A.μ0) (O i) hO.2
    have hsurj : Function.Surjective (O i).jL := by
      intro x
      have hx : (x : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hO.1 ▸ x.2
      obtain ⟨y, hy⟩ := hx
      refine ⟨y, Subtype.ext ?_⟩
      have := RingHom.congr_fun hO.2.lift.field y
      exact this.trans hy
    have hsame : ExtC R i (inC (O i).c') (O i).c0' cM :=
      extC_down R i (O i).jL jL (inC (O i).c') (inC c') hO.2.lift.field hjL hsurj (c0L i) (O i).c0' c0' hc0O hc0 cM hcM
    have e0 : cM = _ := huO cM hsame
    intro c
    constructor
    · intro hc'
      rw [huO c hc', ← e0]
      exact hcM
    · intro hc'
      rw [huM c hc']
      exact hsame
  · have er : rep t' = rep t := hrepE t t' e
    have key : ∀ a b : T0, a = b → ∀ (fa : Rul (d a).Xo₂ (d a).c₂) (fb : Rul (d b).Xo₂ (d b).c₂),
        ∃ cx : Rul (d b).Xo₂ (d b).c₂, ({ d a with cδ := fa } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank) =
          { ({ d b with cδ := fb } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank) with cδ := cx } := by
      rintro a _ rfl fa fb
      exact ⟨fa, rfl⟩
    have keyK : ∀ {β : Type} (g : ∀ a, Cl a → β) (a b : T0) (hab : a = b) (k : Cl a), g b (cast (congrArg Cl hab) k) = g a k := by
      rintro β g a _ rfl k
      rfl
    refine ⟨Equiv.cast (congrArg Cl er.symm), key _ _ er (f t') (f t), congr_arg_heq U er, congr_arg_heq dict er,
      congrArg bad er, congrArg vol er, fun k => ⟨keyK Lh _ _ er.symm k, keyK La _ _ er.symm k, keyK Nc _ _ er.symm k,
      keyK gam _ _ er.symm k⟩⟩

end GlobalTheory.PinsNormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRecordCgTrueT
section
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain GlobalTheory.LocGL GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Loc
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem good_loc_ofChar (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) :
    UpperTheory.Zero.LLC.Good (⟨1, ParLaws.toCl ((CG.ofChar χ).loc w)⟩ : IrrGL (w.adicCompletion E)) := by
  have h : (⟨1, ParLaws.toCl ((CG.ofChar χ).loc w)⟩ : IrrGL (w.adicCompletion E)) =
      IrrGL.ofChar (χ.loc w) (ParLaws.isSmoothChar_loc χ w) := ParLawsT.cls_loc_eq_of_isLocComp (CG.isLoc_ofChar χ w)
  rw [h]
  exact ⟨_, hasSupport_self (IrrGL.isCusp_ofChar _ _), fun y hy => Or.inl (by rw [Multiset.mem_singleton.1 hy]; rfl)⟩

theorem cls_loc_twist (π : CG E a) (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) :
    (⟨a, ParLaws.toCl ((π.twist χ).loc w)⟩ : IrrGL (w.adicCompletion E)) =
      IrrGL.tw ⟨a, ParLaws.toCl (π.loc w)⟩ (χ.loc w) (ParLaws.isSmoothChar_loc χ w) := by
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL E a π w
  refine (ParLawsT.cls_loc_eq_of_isLocComp (hσ.twist χ)).trans ?_
  rw [show (⟨a, ParLaws.toCl (CG.loc (Quotient.mk _ π) w)⟩ : IrrGL (w.adicCompletion E)) = _ from
    ParLawsT.cls_loc_eq_of_isLocComp hσ]
  exact (IrrGL.tw_of σ.ρ σ.smooth σ.irred _ _).symm

end Loc

section Host
variable {R : Ranks} {H : Formalism.BasicNotions.Host R} {a : ℕ}

theorem goodAll_one (χ : HostCGu H 1) : GoodAll χ := fun w => by
  haveI := host_isCMField H
  have h := good_loc_ofChar χ.1.toChar w
  rwa [CG.ofChar_toChar] at h

theorem goodAll_tw_iff (π : HostCGu H a) (χ : HostCGu H 1) :
    haveI := host_isCMField H; GoodAll (H := H) (π.tw χ) ↔ GoodAll π := by
  haveI := host_isCMField H
  refine forall_congr' fun w => ?_
  have h := cls_loc_twist π.1 χ.1.toChar w
  have h2 := GlobalTheory.RecT.good_tw_iff (⟨a, ParLaws.toCl (π.1.loc w)⟩ : IrrGL (w.adicCompletion H.E)) (χ.1.toChar.loc w)
    (ParLaws.isSmoothChar_loc _ w)
  rw [← h] at h2
  exact h2

end Host

section Char
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsTotallyComplex E]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem locParT_unr (hT : UpperTheory.Zero.LLC.RecTExists) (χ : HChar E) (h : IsPlaceOver A w) (hu : χ.UnrAt w) :
    (ParLawsT.locParT hT (CG.ofChar χ) h).unr ∧
      (ParLawsT.locParT hT (CG.ofChar χ) h).frobEig = {(((χ.val w)⁻¹ : ℂˣ) : ℂ)} := by
  have e : χ.loc w = SmGL.unrChar (w.adicCompletion E) (χ.val w) := by
    refine MonoidHom.ext fun x => ?_
    have h2 := unif_spec w
    have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
    have h1 : IsUnitAt w (x * (atFin w (unif w) ^ ord (w.adicCompletion E) x)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
        map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, SphCompletion.ord_completion]
      simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
      rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
    have h3 := hu _ h1
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
    exact h3
  obtain ⟨a, ha, H⟩ := ParLawsT.isRecT_locRecT hT h
  have e2 : ParLawsT.locParT hT (CG.ofChar χ) h = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
    rw [ParLawsT.locParT_ofChar_eq, H.one]
    have : ∀ (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : WeilDeligne.IsSmooth (ξ.comp a)),
        ξ = SmGL.unrChar (w.adicCompletion E) (χ.val w) →
        WD.lpOfChar h (ξ.comp a) hξ = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
      rintro ξ hξ rfl
      exact Test.lpOfChar_unrChar ha _ _
    exact this _ _ e
  rw [e2, WD.frobEig_diag]
  exact ⟨(WD.unr_mk _).2 (WDRep.unr_diag _), by simp⟩

end Char

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

def trueKT (hT : UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (η η' : HostCGu D.host 1)
    (h1 : ∀ w, (ParLawsT.locGT hT D.nd.plOm η w).unr)
    (h2 : ∀ w, ¬ IsSplitPl D.host w → (ParLawsT.locGT hT D.nd.plOm η w).frobEig = {-1})
    (h3 : ∀ w, (ParLawsT.locGT hT D.nd.plOm η' w).unr ∧
      (ParLawsT.locGT hT D.nd.plOm η' w).frobEig = (ParLawsT.locGT hT D.nd.plOm η w).frobEig.map (·⁻¹))
    (h4 : ∀ w w', IsSplitPl D.host w → IsConjPl D.host w w' → ∀ a b : ℂ,
      (ParLawsT.locGT hT D.nd.plOm η w).frobEig = {a} →
      (ParLawsT.locGT hT D.nd.plOm η w').frobEig = {b} → a * b = 1) : CGK D.naut :=
  haveI := host_isCMField D.host
  have L := ParLawsT.lawsT hT GlobalTheory.automorphicFormsFiniteGL D.host D.nd.Om D.nd.plOm
  have U : ∀ {a} (π : HostCGu D.host a) w, D.naut.unr ((T.e w).symm (ParLawsT.locGT hT D.nd.plOm π w)) ↔
      (ParLawsT.locGT hT D.nd.plOm π w).unr :=
    fun π w => by rw [T.unr, Equiv.apply_symm_apply]
  have Fr : ∀ {a} (π : HostCGu D.host a) w, (ParLawsT.locGT hT D.nd.plOm π w).unr →
      D.naut.frobEig ((T.e w).symm (ParLawsT.locGT hT D.nd.plOm π w)) = (ParLawsT.locGT hT D.nd.plOm π w).frobEig :=
    fun π w h => by rw [T.frobEig _ _ ((U π w).2 h), Equiv.apply_symm_apply]
  have Dm : ∀ {a} (π : HostCGu D.host a) w, D.naut.lpDim ((T.e w).symm (ParLawsT.locGT hT D.nd.plOm π w)) = a :=
    fun π w => by rw [← T.dim, Equiv.apply_symm_apply]; exact L.1 π w
  { CG := fun a => {π : HostCGu D.host a // 0 < a ∧ GoodAll π}
    csd := fun π => π.1.IsCsd
    ralg := fun π => π.1.IsRegAlg
    locG := fun π w => (T.e w).symm (ParLawsT.locGT hT D.nd.plOm π.1 w)
    locG_dim := fun π w => Dm π.1 w
    locG_unr_ae := fun π => (L.2.1 π.1).mono fun w h => (U π.1 w).2 h
    tw := fun π χ => ⟨π.1.tw χ.1, π.2.1, (goodAll_tw_iff π.1 χ.1).2 π.2.2⟩
    locG_tw := fun π χ w => (T.e w).injective (by
      rw [T.char _ _ _ (Dm χ.1 w), Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact L.2.2.1 π.1 χ.1 w (π.2.2 w))
    infG := fun π τ => π.1.infChar τ
    infG_card := fun π => L.2.2.2.1 π.1
    ralg_def := fun π => L.2.2.2.2.1 π.1
    infG_tw := fun π χ => L.2.2.2.2.2.1 π.1 χ.1
    csd_tw := fun π χ => L.2.2.2.2.2.2.1 π.1 χ.1
    csd_unr := fun π w w' hπ hc hu => by
      have h := L.2.2.2.2.2.2.2.1 π.1 w w' hπ hc ((U π.1 w).1 hu)
      exact ⟨(U π.1 w').2 h.1, by rw [Fr π.1 w' h.1, Fr π.1 w ((U π.1 w).1 hu)]; exact h.2⟩
    etaT := ⟨η, one_pos, goodAll_one η⟩
    etaTinv := ⟨η', one_pos, goodAll_one η'⟩
    etaT_unr := fun w => (U η w).2 (h1 w)
    etaT_inert := fun w h => by rw [Fr η w (h1 w)]; exact h2 w h
    etaTinv_def := fun w => ⟨(U η' w).2 (h3 w).1, by rw [Fr η' w (h3 w).1, Fr η w (h1 w)]; exact (h3 w).2⟩
    etaT_split := fun w w' hs hc a b ha hb => by
      rw [Fr η w (h1 w)] at ha; rw [Fr η w' (h1 w')] at hb; exact h4 w w' hs hc a b ha hb }

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

def trueCGT (hT : UpperTheory.Zero.LLC.RecTExists) (D : D7) (hE : IsEmpty D.nd.Loc) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (η η' h1 h2 h3 h4) :
    CGTrueT hT (setCG D hE (trueKT hT D T η η' h1 h2 h3 h4)) (wdCG hE _ T) where
  e := fun _ => Function.Embedding.subtype _
  good := fun _ π => π.2.2
  surj := fun _ h π hπ => ⟨⟨π, h, hπ⟩, rfl⟩
  zero := ⟨fun π => lt_irrefl 0 π.2.1⟩
  loc := fun _ _ w => (T.e w).apply_symm_apply _
  tw := fun _ _ _ => rfl
  inf := fun _ _ _ => rfl
  csd := fun _ _ => Iff.rfl

set_option synthInstance.maxHeartbeats 400000 in

theorem etaLawsT (hT : UpperTheory.Zero.LLC.RecTExists) (D : D7) {χ : HChar D.host.E} (hχ : IsEtaT D.host χ) :
    haveI := host_isCMField D.host
    ∃ η η' : HostCGu D.host 1, η.1 = CG.ofChar χ ∧ η'.1 = CG.ofChar χ⁻¹ ∧
      (∀ w, (ParLawsT.locGT hT D.nd.plOm η w).unr) ∧
      (∀ w, ¬ IsSplitPl D.host w → (ParLawsT.locGT hT D.nd.plOm η w).frobEig = {-1}) ∧
      (∀ w, (ParLawsT.locGT hT D.nd.plOm η' w).unr ∧
        (ParLawsT.locGT hT D.nd.plOm η' w).frobEig = (ParLawsT.locGT hT D.nd.plOm η w).frobEig.map (·⁻¹)) ∧
      (∀ w w', IsSplitPl D.host w → IsConjPl D.host w w' → ∀ a b : ℂ,
        (ParLawsT.locGT hT D.nd.plOm η w).frobEig = {a} →
        (ParLawsT.locGT hT D.nd.plOm η w').frobEig = {b} → a * b = 1) := by
  haveI := host_isCMField D.host
  have hi : (χ⁻¹).IsUnitary := fun x => by
    have := hχ.unitary x
    change ‖(((χ.1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, this, inv_one]
  have hu : ∀ w, (χ⁻¹).UnrAt w := fun w x hx => by rw [HChar.loc_inv, hχ.unr w x hx, inv_one]
  have P := fun w => locParT_unr hT χ (D.nd.plOm.2 w) (hχ.unr w)
  have Q := fun w => locParT_unr hT χ⁻¹ (D.nd.plOm.2 w) (hu w)
  refine ⟨⟨CG.ofChar χ, CG.isUnitary_ofChar hχ.unitary⟩, ⟨CG.ofChar χ⁻¹, CG.isUnitary_ofChar hi⟩, rfl, rfl,
    fun w => (P w).1, fun w hw => (P w).2.trans ?_, fun w => ⟨(Q w).1, (Q w).2.trans ?_⟩,
    fun w w' hw hc a b ha hb => ?_⟩
  · rw [CGTrueModel.val_inert hχ hw]; simp
  · refine Eq.trans ?_ (congrArg (Multiset.map (·⁻¹)) (P w).2).symm
    simp
  · have ha' := (P w).2.symm.trans ha
    have hb' := (P w').2.symm.trans hb
    rw [Multiset.singleton_inj] at ha' hb'
    rw [← ha', ← hb', ← Units.val_mul, ← mul_inv, CGTrueModel.val_split hχ hw hc, inv_one, Units.val_one]

theorem CGTrueT.ralg {hT D T} (C : CGTrueT hT D T) a (π : D.naut.CG a) :
    haveI := host_isCMField D.host; D.naut.ralg π ↔ (C.e a π).IsRegAlg := by
  rw [D.naut.ralg_def]; simp only [C.inf]; exact (GlobalTheory.CuspRep.CG.isRegAlg_iff _).symm

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterValueAtConjugatePlacePow
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjLocVal

theorem value_at_conj_place : ∀ (D : D7) (PP : Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (n : ℕ) (y : (AE D)ˣ), Formalism.L2.NTheta.IsIdemAt e PP → ϖ ∈ PP.asIdeal → ϖ ∉ PP.asIdeal ^ 2 → ChrEq c χ → χ.UnrAt (Formalism.L2.DIV.conjPl PP) → (y : AE D) = 1 + cA D e * (incA D (star (ϖ : D.host.E)) ^ n - 1) → ((c y : Circle) : ℂ) = ((χ.val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) ^ n := by
  intro D PP e ϖ c χ n y he h1 h2 hc hU hy
  obtain ⟨⟨e1, e2, v, ε, hε, e3⟩, e4⟩ := Formalism.IndefR.Fin.LevelGroupLemmas.isIdemAt_conj he
  have hpl : Formalism.L2.JoinChr.IsPlIdem D (cA D e) (Formalism.L2.DIV.conjPl PP) := ⟨e1, ⟨v, ε, hε, Or.inl ⟨e2, e3⟩⟩, e4⟩
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact h2 (zero_mem _)
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  have hs0 : star (ϖ : D.host.E) ≠ 0 := star_ne_zero.2 hϖE
  set k : D.host.Eˣ := Units.mk0 (star (ϖ : D.host.E)) hs0 with hk
  have hy' : (y : AE D) = Formalism.L2.JoinChr.locE D (cA D e) ((k ^ n : D.host.Eˣ) : D.host.E) := by
    rw [hy, Formalism.L2.JoinChr.locE, Units.val_pow_eq_pow_val, map_pow]
    rfl
  rw [hc.2 _ _ hpl (k ^ n) y hy', map_pow, Units.val_pow_eq_pow_val]
  congr 1
  have hmem : Formalism.L2.DIV.starO ϖ ∈ (Formalism.L2.DIV.conjPl PP).asIdeal := by
    show Formalism.L2.DIV.starO (Formalism.L2.DIV.starO ϖ) ∈ PP.asIdeal
    rw [Formalism.L2.DIV.starO_starO]; exact h1
  have hnsq : Formalism.L2.DIV.starO ϖ ∉ (Formalism.L2.DIV.conjPl PP).asIdeal ^ 2 := by
    intro hm
    have hm' := Ideal.le_comap_pow (f := Formalism.L2.DIV.starOHom) (K := PP.asIdeal) 2 hm
    rw [Ideal.mem_comap] at hm'
    apply h2
    have : Formalism.L2.DIV.starOHom (Formalism.L2.DIV.starO ϖ) = ϖ := Formalism.L2.DIV.starO_starO ϖ
    rwa [this] at hm'
  have hunif : Formalism.L2.Host.IsUnifAt (Formalism.L2.DIV.conjPl PP) (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) k) := by
    show Valued.v (((star (ϖ : D.host.E) : D.host.E)) : (Formalism.L2.DIV.conjPl PP).adicCompletion D.host.E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← Formalism.L2.DIV.starO_coe,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact GlobalTheory.LatIntFacts.intValuation_uniformiser _ hmem hnsq
  have hval : χ.loc (Formalism.L2.DIV.conjPl PP) (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) k) = χ.val (Formalism.L2.DIV.conjPl PP) := by
    have hu : Formalism.L2.Host.IsUnitAt (Formalism.L2.DIV.conjPl PP)
        (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) k * (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) (Formalism.L2.Host.unif (Formalism.L2.DIV.conjPl PP)))⁻¹) := by
      have h2' := Formalism.L2.Host.unif_spec (Formalism.L2.DIV.conjPl PP)
      unfold Formalism.L2.Host.IsUnitAt
      unfold Formalism.L2.Host.IsUnifAt at hunif h2'
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hunif, h2']
      exact mul_inv_cancel₀ (by simp)
    have h3 := hU _ hu
    rw [map_mul, map_inv, mul_inv_eq_one] at h3
    exact h3
  show ((χ.loc (Formalism.L2.DIV.conjPl PP) (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) k) : ℂˣ) : ℂ) = _
  rw [hval]

end GlobalTheory.ConjLocVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOneOfMemLocalUnitBallSide
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nrm_le_one_of_mem_locBall_pts : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), ∀ f ∈ locBall YS fw iC b j, ∀ y : (Rl.FW j).Pt (placeC YS iC b), (Rl.FW j).nrm (placeC YS iC b) y ⟨(YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1, ((YS.fi j).wk _).1 (show ↥(S.A ((j : ℕ) + 1)).WK from f).2⟩ ≤ 1 := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j f hf y
  have h := nrm_le_one_of_mem_locBall YS fw iC b j hf y
  have he : fw.e j (cuspOf YS fw j f) = ⟨(YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1,
      ((YS.fi j).wk _).1 (show ↥(S.A ((j : ℕ) + 1)).WK from f).2⟩ :=
    Subtype.ext (e_cuspOf YS fw j f)
  rw [he] at h
  exact h

end GlobalTheory.GeoTie
end
end

