import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0552
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorValuedLiftFieldChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0551
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalDivX
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndicesPairingLengthsVanishOffTwistedPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0553
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0241
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBcStages
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.Mem GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.RealGeo GlobalTheory.OneMapAll GlobalTheory.FieldBC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmExt

theorem levOver_cast' {D : D7} {G : Type} [Group G] {i : Fin D.R.m} {Pg₁ Pg₂ : Finset (Formalism.L2.DIV.Pl D.host.E)}
    {β₁ β₂ : ∀ i, GL (Fin (Wc D i).rank) (Lev.EAf D)} {e₁ : G ≃* G0 Pg₁ D.R.r} {e₂ : G ≃* G0 Pg₂ D.R.r}
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Dw : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
    {ι : ∀ j : ℕ, (Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)} (hP : HEq Pg₂ Pg₁) (hβ : HEq β₂ β₁) (he : HEq e₂ e₁)
    {lev : G → (Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Dw ((i : ℕ) + 1)).La} (h : LevOver D i Pg₁ β₁ e₁ l Dw ι lev) :
    LevOver D i Pg₂ β₂ e₂ l Dw ι lev := by
  cases hP; cases hβ; cases he
  exact h

set_option maxHeartbeats 4000000 in

theorem exists_bc_stages (X X' : Stages) (hP : X'.B.toPre = X.B.toPre) (hLL : Set.range X.B.embLL ⊆ Set.range X'.B.embLL)
    {G : Type} [Group G] [Fintype G] {Pl0 T0 Pl0' T0' : Type} {A : FamIn X.toD7.what₂.LL G Pl0 T0 X.toD7.R.m}
    {A' : FamIn X'.toD7.what₂.LL G Pl0' T0' X'.toD7.R.m} (T : CoreJ X.toD7) [Algebra T.Q.c.F X.toD7.what₂.LL]
    (T' : CoreJ X'.toD7) [alg' : Algebra T'.Q.c.F X'.toD7.what₂.LL] (R : RealDat X.toD7 A T.Q.c.F) (R' : RealDat X'.toD7 A' T'.Q.c.F)
    (eH : HEq T'.Q.H T.Q.H) (el : HEq T'.Q.l T.Q.l) (ec : HEq T'.Q.c T.Q.c) (eD : HEq T'.Q.Dw T.Q.Dw) (eX : HEq T'.Q.Xo T.Q.Xo)
    (ex : HEq T'.x₀ T.x₀) (eι : HEq T'.iota T.iota) (ePg : HEq R'.Pg R.Pg) (eβV : HEq R'.βV R.βV) (eβW : HEq R'.βW R.βW)
    (eG : HEq R'.eG R.eG) (emu : HEq R'.C.mu0 R.C.mu0) (eeta : HEq R'.C.eta R.C.eta)
    {κ : ∀ i : Fin X.toD7.R.m, WeightFamilies.Wt X.toD7 ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin X.toD7.R.m) (σ : X.toD7.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    {κ' : ∀ i : Fin X'.toD7.R.m, WeightFamilies.Wt X'.toD7 ((i : ℕ) + 1)}
    {v₀' : ∀ (i : Fin X'.toD7.R.m) (σ : X'.toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec}
    (hL : R.toLevCh.Is A.μ0) (hV : R.models_HV) (hκ : KapIs κ) (hL' : R'.toLevCh.Is A'.μ0) (hM' : R'.IsModels) (hF' : R'.fam_tie)
    (ht' : TieIn T' R' κ' v₀') (i : Fin X.toD7.R.m) (i' : Fin X'.toD7.R.m) (hi : (i : ℕ) = i')
    (eW : HEq (R'.cV i').W (R.cV i).W) (en : HEq (R'.cV i').nW (R.cV i).nW) (ei : HEq (R'.cV i').iW (R.cV i).iW)
    (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (hOF : O.c'.F = X.toD7.what₂.embLL.toRatAlgHom.fieldRange)
    (hO : O.Pins (κ i) (v₀ i (sg0 X.toD7 A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) (P : Prop)
    (hc : ∀ c0L, CoefFam R c0L → P ∨ ∃ c0L', CoefFam R' c0L' ∧
      ∀ (v : VsV X.toD7 i X.toD7.what₂.LL) (v' : VsV X'.toD7 i' X'.toD7.what₂.LL),
        HEq (MvPolynomial.map X'.toD7.what₂.embLL v'.1) (MvPolynomial.map X.toD7.what₂.embLL v.1) → HEq (c0L' i' v') (c0L i v)) :
    ∃ O' : OMDat T'.toCore R' i' Unit (fun _ => A'.μ0), O'.c'.F = X'.toD7.what₂.embLL.toRatAlgHom.fieldRange ∧
      O'.Pins (κ' i') (v₀' i' (sg0 X'.toD7 A')) (iotaW T' i') (T'.x₀ ((i' : ℕ) + 1) O'.s0) ∧
      IsBCOf O' (v₀' i' (sg0 X'.toD7 A')) O (v₀ i (sg0 X.toD7 A)) (κ i) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) P := by
  obtain ⟨c₃, hF₃, h₃⟩ := GlobalTheory.RefPins.exists_coeff_rows T' ht'.alg ht'.laws.pins.2.2.1
  have hmem : ∀ y, X'.toD7.what₂.embLL y ∈ c₃.F := fun y => hF₃.ge ⟨y, rfl⟩
  let jL' : X'.toD7.what₂.LL →+* c₃.F := X'.toD7.what₂.embLL.codRestrict c₃.F hmem
  have hjL' : (inC c₃).comp jL' = X'.toD7.what₂.embLL := RingHom.ext fun _ => rfl
  have sj' : Function.Surjective jL' := fun y => by
    obtain ⟨x, hx⟩ := hF₃.le y.2
    exact ⟨x, Subtype.ext hx⟩
  have sj : Function.Surjective O.jL := fun y => by
    obtain ⟨x, hx⟩ := hOF.le y.2
    exact ⟨x, Subtype.ext ((RingHom.congr_fun hO.lift.field x).trans hx)⟩
  have hs : O.c'.F ≤ c₃.F := fun y hy => by
    obtain ⟨x, hx⟩ := hOF.le hy
    obtain ⟨x', hx'⟩ := hLL ⟨x, hx⟩
    exact hF₃.ge ⟨x', hx'⟩
  have hQ := GlobalTheory.RefPins.places_ref R hL
  have hQ' := GlobalTheory.RefPins.places_ref R' hL'
  have hV₃ : T'.V ((i' : ℕ) + 1) (sOv T'.toCore c₃ h₃) = Wc X'.toD7 i' := ht'.laws.spaceW _ (inR i') _ rfl
  obtain ⟨g, r, c0L, hT, hbc⟩ := hO.lift.c0
  have hx1 := hL.xi A.μ0
  have hx1' := hL'.xi A'.μ0
  rw [hL.xi_base] at hx1
  rw [hL'.xi_base] at hx1'
  have hplace : ∀ (c0L') (c0'' : VsV X'.toD7 i' c₃.F →ₛₗ[inC c₃] (R'.cV i').W), CoefFam R' c0L' →
      CoefficientBaseChange R' i' jL' (inC c₃) (c0L' i') c0'' → ∀ (Cl : Type) [Fintype Cl] (h : Cl → GA X'.toD7 (Vc X'.toD7 i')),
      PlaceEx R' i' A'.μ0 h c0'' := by
    rintro c0L' c0'' ⟨_, _, htie⟩ hc0 Cl _ h
    exact GlobalTheory.RationalValues.placeEx_of_type_mem R' i' jL' (inC c₃) A'.μ0 h c0'' hM'.jV htie hc0
      (GlobalTheory.RationalValues.type_mem R' i' A'.μ0 _
        (fun PP hPP x => by
          obtain ⟨y, hy⟩ := GlobalTheory.RefPins.chiVal_of_tie T' R' κ' v₀' hL' ht' i' PP hPP x
          exact ⟨jL' y, hy⟩)
        fun PP hPP => absurd (hQ' ▸ hPP) (Finset.notMem_empty _))
  have hv0' := ht'.hv₀ i' (sg0 X'.toD7 A')
  have hκ' := ht'.kap i'
  clear ht'
  have hc' : ∃ c0L', CoefFam R' c0L' ∧ (P ∨ ∀ (v : VsV X.toD7 i X.toD7.what₂.LL) (v' : VsV X'.toD7 i' X'.toD7.what₂.LL),
        HEq (MvPolynomial.map X'.toD7.what₂.embLL v'.1) (MvPolynomial.map X.toD7.what₂.embLL v.1) → HEq (c0L' i' v') (c0L i v)) := by
    rcases hc c0L ⟨g, r, hT⟩ with h | ⟨c, h1, h2⟩
    · obtain ⟨g', r', c, h1⟩ := hF'
      exact ⟨c, ⟨g', r', h1⟩, Or.inl h⟩
    · exact ⟨c, h1, Or.inr h2⟩
  clear hc
  obtain ⟨c0L', hT', hag⟩ := hc'
  obtain ⟨c0'', hbc'⟩ := GlobalTheory.Mem.PlaceVal.exists_ext_VV (W := (R'.cV i').W) jL' (inC c₃) hjL' (lamV X'.toD7 i') (c0L' i')
  have hpl' := hplace c0L' c0'' hT' hbc'
  clear hplace
  obtain ⟨B', C', W', V', S', N', G'⟩ := X'
  rcases B' with ⟨P'⟩
  change P' = X.B.toPre at hP
  subst hP
  obtain ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V'', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := T'
  dsimp only at eH el ec eD eX ex eι
  obtain rfl := eq_of_heq eH
  obtain rfl := eq_of_heq el
  obtain rfl := eq_of_heq ec
  obtain rfl := eq_of_heq eD
  obtain rfl := eq_of_heq eX
  obtain rfl := eq_of_heq ex
  obtain rfl := eq_of_heq eι
  obtain rfl : i = i' := Fin.ext hi
  have h0 : ∃ c0₃ : VsV X.toD7 i c₃.F →ₛₗ[inC c₃] (R.cV i).W, (∀ (v : VsV X.toD7 i O.c'.F) (v' : VsV X.toD7 i c₃.F),
      (v' : Pol c₃.F X.toD7.what₂.Tau (Vc X.toD7 i).rank) =
        MvPolynomial.map (incF O.c' c₃ hs) (v : Pol O.c'.F X.toD7.what₂.Tau (Vc X.toD7 i).rank) → c0₃ v' = O.c0' v) ∧
      (HEq c0'' c0₃ ∨ P) := by
    rcases hag with hp | hag
    · obtain ⟨c0₃, h⟩ := exists_coef_ext (incF O.c' c₃ hs) (σ := inC O.c') (inC c₃) (fun _ => rfl) (lamV X.toD7 i) O.c0'
      exact ⟨c0₃, h, Or.inr hp⟩
    · obtain ⟨c0₃, h1, h2⟩ := exists_cast_map (V := VsV X.toD7 i c₃.F) (σ := inC c₃) (R.cV i).nW (R.cV i).iW (R'.cV i).nW (R'.cV i).iW
        eW en ei ((by with_unfolding_all exact (c0'' :)))
      refine ⟨c0₃, fun v v' e => eq_of_heq ((h2 v').symm.trans ?_), Or.inl ((by with_unfolding_all exact (h1 :)))⟩
      exact coef_agree (W' := (R'.cV i).W) (lamV X.toD7 i) O.jL jL' (incF O.c' c₃ hs) hO.lift.field hjL' (RingHom.ext fun _ => rfl) sj sj'
        (cL' := (by with_unfolding_all exact ((c0L' i) :))) hbc ((by with_unfolding_all exact (hbc' :))) ((by with_unfolding_all exact (hag :))) v v' e
  obtain ⟨c0₃, hc0, hor⟩ := h0
  obtain ⟨io₃, hw₃, h, J', hB⟩ := exists_isBC O c₃ hs c0₃ (v₀ i (sg0 X.toD7 A)) hV hO hc0
  have hM := hB.pins
  have eχ : R'.C.mu0 i * R'.xiH A'.μ0 * R'.C.eta⁻¹ = R.C.mu0 i * R.xiH A.μ0 * R.C.eta⁻¹ := (by with_unfolding_all exact ((congrArg₂ (fun a b : Formalism.L2.Host.HChar X.toD7.host.E => a * b⁻¹)
      (congrArg₂ (fun a b : Formalism.L2.Host.HChar X.toD7.host.E => a * b) (congrFun (eq_of_heq emu) i) (hL'.xi_base.trans hL.xi_base.symm))
      (eq_of_heq eeta)) :))
  have eξ : R'.xi A'.μ0 = R.xi A.μ0 := (GlobalTheory.ChrEqUnique.chrEq_unique X.toD7).2.1 _ _ _ ((by with_unfolding_all exact (hx1' :))) hx1
  have hT1 := (tupOver_iff R A.μ0).2 ⟨repsR_map (incF O.c' c₃ hs) hB.reps, (hM.tuple ()).B, (hM.tuple ()).xi, (hM.tuple ()).phi,
    (hM.tuple ()).half⟩
  have hT2 := tupOver_cast (D := X.toD7) (Pg₂ := R'.Pg) (Q₂ := R'.Q A'.μ0) (βV₂ := (by with_unfolding_all exact (R'.βV :))) (βW₂ := (by with_unfolding_all exact (R'.βW :)))
    (ξR₂ := (by with_unfolding_all exact ((R'.xiR A'.μ0) :))) ePg hQ hQ' ((by with_unfolding_all exact (eβV :))) ((by with_unfolding_all exact (eβW :))) eχ eξ hT1
  have hl2 := levOver_cast' (D := X.toD7) (Pg₂ := R'.Pg) (β₂ := (by with_unfolding_all exact (R'.βW :))) (e₂ := (by with_unfolding_all exact (R'.eG :))) ePg ((by with_unfolding_all exact (eβW :))) ((by with_unfolding_all exact (eG :)))
    ((levOver_iff T R i O.lev).2 hO.lift.lev)
  let κ₀ : WeightFamilies.Wt X.toD7 ((i : ℕ) + 1) := ⟨(by with_unfolding_all exact ((κ' i).aP :)), (by with_unfolding_all exact ((κ' i).aM :)), (by with_unfolding_all exact ((κ' i).aPlus_antitone :)), (by with_unfolding_all exact ((κ' i).aM_anti :)), (κ' i).n, (κ' i).n_even⟩
  have ew : wtA κ₀ = wtA (κ i) := wtA_eq _ _
    (funext fun τ => funext fun k => Eq.trans ((by with_unfolding_all exact (((hκ' τ).1 k) :))) ((hκ i τ).1 k).symm)
    (funext fun τ => funext fun k => Eq.trans ((by with_unfolding_all exact (((hκ' τ).2.1 k) :))) ((hκ i τ).2.1 k).symm)
  have hio := hM.io
  rw [← ew] at hio
  let M := bc O c₃ hs c0₃ io₃ hw₃ h (v₀ i (sg0 X.toD7 A))
  refine ⟨@OMDat.mk _ G _ _ Pl0' T0' A' _ alg' R' i Unit _ (c' := c₃) (hle := h₃) (jL := jL') (hV := hV₃) (c0' := c0'') (lev := (by with_unfolding_all exact (M.lev :)))
    (dδ := (by with_unfolding_all exact (M.dδ :))) (Cl' := M.Cl') (fCl := M.fCl) (bad := M.bad) (Lh := (by with_unfolding_all exact (M.Lh :))) (La := (by with_unfolding_all exact (M.La :))) (Nc := (by with_unfolding_all exact (M.Nc :))) (gam := (by with_unfolding_all exact (M.gam :)))
    (vol := (by with_unfolding_all exact (M.vol :))) (ep := (by with_unfolding_all exact (M.ep :))) (B := (by with_unfolding_all exact (M.B :))) (epF := (by with_unfolding_all exact (M.epF :))) (io := (by with_unfolding_all exact (M.io :))) (hw := (by with_unfolding_all exact (M.hw :))) (φ := (by with_unfolding_all exact (M.φ :)))
    (w := (by with_unfolding_all exact (M.w :))) (U₂ := (by with_unfolding_all exact (M.U₂ :))) (dict₂ := (by with_unfolding_all exact (M.dict₂ :))) (xi := (by with_unfolding_all exact (M.xi :)))
    (thAd := fun _ => thAdOf R' i A'.μ0 (Cl := O.Cl' ()) ((by with_unfolding_all exact (h :))) c0'' (v₀' i (sg0 _ A')))
    (Plc := fun _ x => ∃ x₀, Place R' i A'.μ0 (Cl := O.Cl' ()) ((by with_unfolding_all exact (h :))) c0'' (jVx R' i A'.μ0 x₀) x), hF₃, ?_, ?_⟩
  · have hth := thAdIs_thAdOf R' i A'.μ0 (Cl := O.Cl' ()) ((by with_unfolding_all exact (h :))) c0'' hM'.HV (J' := (by with_unfolding_all exact (J' :))) ((by with_unfolding_all exact (hT2.1.2.2.1 :))) ((by with_unfolding_all exact (hT2.1.2.2.2.2.2.1 :)))
      (v₀' i (sg0 _ A'))
    obtain ⟨g', r', hT'⟩ := hT'
    apply (config := { synthAssignedInstances := false }) OMDat.Pins.mk
    case lift =>
      apply (config := { synthAssignedInstances := false }) ThPinsR.mk
      case field => exact hjL'
      case std => exact (by with_unfolding_all exact (hO.lift.std :))
      case v0 => exact hv0'
      case lev => exact (by with_unfolding_all exact (hl2 :))
      case c0 => exact ⟨g', r', c0L', hT', hbc'⟩
    case tuple =>
      intro t
      apply (config := { synthAssignedInstances := false }) ThPinsT.mk
      case reps => exact ⟨(by with_unfolding_all exact (h :)), (by with_unfolding_all exact (J' :)), (by with_unfolding_all exact (hT2.1 :)), (by with_unfolding_all exact ((hpl' (O.Cl' ()) ((by with_unfolding_all exact (h :)))) :)), (by with_unfolding_all exact (hth :)), fun _ => Iff.rfl⟩
      case B => exact (by with_unfolding_all exact (hT2.2.1 :))
      case xi => exact (by with_unfolding_all exact (hT2.2.2.1 :))
      case phi => exact (by with_unfolding_all exact (hT2.2.2.2.1 :))
      case half => exact (by with_unfolding_all exact (hT2.2.2.2.2 :))
    case act => exact (by with_unfolding_all exact (hM.act :))
    case bad => exact (by with_unfolding_all exact (hM.bad :))
    case reps => exact (by with_unfolding_all exact (hM.reps :))
    case ep => exact (by with_unfolding_all exact (hM.ep :))
    case io => exact (by with_unfolding_all exact (hio :))
    case w => exact (by with_unfolding_all exact (hM.w :))
    case cov => exact (by with_unfolding_all exact (hM.cov :))
    case cxi => exact (by with_unfolding_all exact (hM.cxi :))
    case model₂ => exact (by with_unfolding_all exact (hM.model₂ :))
  · have hth := thAdIs_thAdOf R' i A'.μ0 (Cl := O.Cl' ()) ((by with_unfolding_all exact (h :))) c0'' hM'.HV (J' := (by with_unfolding_all exact (J' :))) ((by with_unfolding_all exact (hT2.1.2.2.1 :))) ((by with_unfolding_all exact (hT2.1.2.2.2.2.2.1 :)))
      (v₀' i (sg0 _ A'))
    refine ⟨c₃, hs, c0₃, io₃, hw₃, h, J', hB, ?_, hor, (by with_unfolding_all exact (h :)), (by with_unfolding_all exact (J' :)), (by with_unfolding_all exact ((HEq.refl h) :)), (by with_unfolding_all exact ((HEq.refl J') :)), (by with_unfolding_all exact (hT2.1 :)),
      (by with_unfolding_all exact ((hpl' (O.Cl' ()) ((by with_unfolding_all exact (h :)))) :)), (by with_unfolding_all exact (hth :)), fun _ => Iff.rfl⟩
    exact ⟨(by with_unfolding_all exact ((HEq.refl M.c') :)), (by with_unfolding_all exact ((HEq.refl M.lev) :)), (by with_unfolding_all exact ((HEq.refl M.dδ) :)), rfl, (by with_unfolding_all exact ((HEq.refl M.fCl) :)), rfl, (by with_unfolding_all exact ((HEq.refl M.Lh) :)),
      (by with_unfolding_all exact ((HEq.refl M.La) :)), (by with_unfolding_all exact ((HEq.refl M.Nc) :)), (by with_unfolding_all exact ((HEq.refl M.gam) :)), (by with_unfolding_all exact ((HEq.refl M.vol) :)), (by with_unfolding_all exact ((HEq.refl M.ep) :)), (by with_unfolding_all exact ((HEq.refl M.B) :)),
      (by with_unfolding_all exact ((HEq.refl M.epF) :)), (by with_unfolding_all exact ((HEq.refl M.io) :)), (by with_unfolding_all exact ((HEq.refl M.hw) :)), (by with_unfolding_all exact ((HEq.refl M.φ) :)), (by with_unfolding_all exact ((HEq.refl M.w) :)), (by with_unfolding_all exact ((HEq.refl M.U₂) :)),
      (by with_unfolding_all exact ((HEq.refl M.dict₂) :)), (by with_unfolding_all exact ((HEq.refl M.xi) :))⟩

end GlobalTheory.Mem.R3.Rw.OmExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftFormsLatticeBaseLevelBaseChangeAStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendedData_liftFormsLattice_baseLevel_baseChange_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ G : Matrix (Fin ((z'.R.toCx3 z'.F).dW false j')) (Fin ((z.R.toCx3 z.F).dW false j)) (w'.st Z').toD7.what₂.LL, Function.Bijective G.mulVec ∧
          (z'.R.toCx3 z'.F).M false j' = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin ((z.R.toCx3 z.F).dW false j) → (w.st Z).toD7.what₂.LL => Matrix.mulVec G fun k => φ (x k)) '' ((z.R.toCx3 z.F).M false j : Set (Fin ((z.R.toCx3 z.F).dW false j) → (w.st Z).toD7.what₂.LL))) ∧
          ∀ y : Fin ((z.R.toCx3 z.F).dW false j) → (w.st Z).toD7.what₂.LL, HEq ((z'.R.toCx3 z'.F).w0C false j' (Formalism.IndefR.Cx.cpt (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.base3.v0.embedding (Matrix.mulVec G fun k => φ (y k)))) ((z.R.toCx3 z.F).w0C false j (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding y))) := by
  first | exact @GlobalTheory.Mem.R3.LiftForms.extendedData_liftFormsLattice_baseLevel_baseChange | exact GlobalTheory.Mem.R3.LiftForms.extendedData_liftFormsLattice_baseLevel_baseChange | (intros; apply GlobalTheory.Mem.R3.LiftForms.extendedData_liftFormsLattice_baseLevel_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherPlacePenultimateChartCharacterInverseValuStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.furtherPlace_penultimateChart_character_inverseValue : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Q → ∀ β (x : (K β).lev.Uloc v), (((K β).lev.chi (GlobalTheory.Mem.Col2.ChartLevel.embU (K β).lev v x) : ℂˣ) : ℂ) * GlobalTheory.Mem.Col2.QChi.valV I l Z a v x.1 = 1 := by
  first | exact @GlobalTheory.Mem.Col2.QChi.chi_embU_mul_valV | exact GlobalTheory.Mem.Col2.QChi.chi_embU_mul_valV | (intros; apply GlobalTheory.Mem.Col2.QChi.chi_embU_mul_valV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricallyIntegralAlgebraicConstantsMemRange
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct

namespace GlobalTheory.GeomIntConst

theorem finrank_eq_one_of_isDomain_tensor {F L : Type} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsDomain (L ⊗[F] L)] : Module.finrank F L = 1 := by
  have hinj : Function.Injective (algebraMap L (L ⊗[F] L)) := (algebraMap L (L ⊗[F] L)).injective
  have hT : IsField (L ⊗[F] L) :=
    (Algebra.IsIntegral.isField_iff_isField hinj).1 (Field.toIsField L)
  let f : L ⊗[F] L →ₐ[L] L := Algebra.TensorProduct.lmul'' F
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h
    obtain ⟨y, hy⟩ := hT.mul_inv_cancel h
    have := congrArg f hy
    rw [map_mul, hx, zero_mul, map_one] at this
    exact zero_ne_one this
  have hs : Function.Surjective f := fun x => ⟨x ⊗ₜ 1, by
    show Algebra.TensorProduct.lmul'' F (x ⊗ₜ[F] (1 : L)) = x
    first
      | simp [Algebra.TensorProduct.lmul''_apply_tmul]
      | exact (Algebra.TensorProduct.lmul'_apply_tmul (R := F) x (1 : L)).trans (mul_one x)⟩
  have e := (LinearEquiv.ofBijective f.toLinearMap ⟨hf, hs⟩).finrank_eq
  rw [Module.finrank_baseChange, Module.finrank_self] at e
  exact e

theorem mem_range_constFn (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F)
    [GeometricallyIntegral p] (b : Y.functionField)
    (hb : ∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn p) b = 0) :
    b ∈ (GlobalTheory.Cartier.constFn p).range := by
  letI : Algebra F Y.functionField := (GlobalTheory.Cartier.constFn p).toAlgebra
  obtain ⟨P, hP, hPb⟩ := hb
  have hint : IsIntegral F b := (show IsAlgebraic F b from ⟨P, hP, hPb⟩).isIntegral
  obtain ⟨V, hV, s₀, hs₀⟩ := Y.presheaf.exists_germ_eq b
  obtain ⟨U, hU, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hV
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  let s : Γ(Y, U) := resG Y hUV s₀
  have hs : GlobalTheory.Cartier.fnOf U hxU s = b := by
    rw [GlobalTheory.Cartier.fnOf_resG]; exact hs₀
  letI : Algebra F Γ(Y, U) := (algX p U).toAlgebra
  have e : (GlobalTheory.Cartier.fnOf U hxU).comp (algebraMap F Γ(Y, U)) = algebraMap F Y.functionField :=
    GlobalTheory.Cartier.fnOf_comp_algX p U hxU
  have hm : Polynomial.aeval s (minpoly F b) = 0 := by
    apply GlobalTheory.Cartier.fnOf_injective U hxU
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂, e, hs, ← Polynomial.aeval_def,
      minpoly.aeval]
  haveI : Fact (Irreducible (minpoly F b)) := ⟨minpoly.irreducible hint⟩
  let φ : AdjoinRoot (minpoly F b) →ₐ[F] Γ(Y, U) := AdjoinRoot.liftAlgHom (minpoly F b) (Algebra.ofId F Γ(Y, U)) s
    (by rw [Polynomial.aeval_def] at hm; exact hm)
  have hφ : Function.Injective φ := φ.toRingHom.injective

  let g := Spec.map (CommRingCat.ofHom (algebraMap F (AdjoinRoot (minpoly F b))))
  have hg : hU.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (algebraMap F Γ(Y, U))) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)
    rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have hYL : IsIntegral (pullback p g) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback p g)
  have : Surjective g := ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have : Nonempty ((pullback hU.fromSpec (pullback.fst p g) : Scheme.{0})) := by
    obtain ⟨z, -⟩ : genericPoint Y ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hxU
    have hz : z ∈ Set.range (pullback.fst hU.fromSpec (pullback.fst p g)) := by
      rw [Scheme.Pullback.range_fst]; exact (pullback.fst p g).surjective _
    exact ⟨hz.choose⟩
  haveI := hU.isOpenImmersion_fromSpec
  have : IsIntegral (pullback hU.fromSpec (pullback.fst p g)) :=
    isIntegral_of_isOpenImmersion (pullback.snd hU.fromSpec (pullback.fst p g))
  have : IsIntegral (pullback (hU.fromSpec ≫ p) g) :=
    IsIntegral.of_isIso (pullbackRightPullbackFstIso p g hU.fromSpec).hom
  rw [hg] at this
  have : IsIntegral (Spec (.of (Γ(Y, U) ⊗[F] AdjoinRoot (minpoly F b)))) :=
    IsIntegral.of_isIso (pullbackSpecIso F Γ(Y, U) (AdjoinRoot (minpoly F b))).hom
  have : IsDomain (Γ(Y, U) ⊗[F] AdjoinRoot (minpoly F b)) :=
    (affine_isIntegral_iff (.of (Γ(Y, U) ⊗[F] AdjoinRoot (minpoly F b)))).mp this

  have hinj : Function.Injective (Algebra.TensorProduct.map φ
      (AlgHom.id F (AdjoinRoot (minpoly F b)))) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := AdjoinRoot (minpoly F b))
      φ.toLinearMap hφ
  have : IsDomain (AdjoinRoot (minpoly F b) ⊗[F] AdjoinRoot (minpoly F b)) :=
    Function.Injective.isDomain (Algebra.TensorProduct.map φ
      (AlgHom.id F (AdjoinRoot (minpoly F b)))).toRingHom hinj
  have hm0 : minpoly F b ≠ 0 := minpoly.ne_zero hint
  have : FiniteDimensional F (AdjoinRoot (minpoly F b)) := (AdjoinRoot.powerBasis hm0).finite
  have h1 := finrank_eq_one_of_isDomain_tensor (F := F) (L := AdjoinRoot (minpoly F b))
  rw [(AdjoinRoot.powerBasis hm0).finrank, AdjoinRoot.powerBasis_dim] at h1
  exact minpoly.natDegree_eq_one_iff.1 h1

end GlobalTheory.GeomIntConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndexZeroOffTwistedPlaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.R3.Rw.St.idx_zero_off_twisted : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), P.Wt = x.m.z.W1 (F0K K.s (w.D x.o.Z)) → ∀ v, v ∉ P.Wt → ∀ j, 1 ≤ j → j ≤ B.R.m →
      (w.D x.o.Z).what₂.Ij (w.D x.o.Z).what₂.mu0 j v = 0 ∧ (w.D x.o.Z).what₂.jw (w.D x.o.Z).what₂.mu0 j v = 0 := by
  intro K B f T w hO hF hP P x hη hW v hv j hj1 hj2
  classical
  let Zr : ReadL x.m.z.R x.m.z.F x.s.p0 x.r.Y := (x.rowsAre hη).Z
  obtain ⟨G, Y, -⟩ := GlobalTheory.PointGeometry.exists_geo (w.st x.o.Z).toD7.what₂.LL
  let Fm : ∀ k, GlobalTheory.ProvisionalDivX.MjForm (w.st x.o.Z).toD7 k := fun k =>
    ⟨mjH Zr k, jM Zr k, mjH_good Zr x.m.intersectionNumber_baseChange k, jM_basis Zr x.m.intersectionNumber_baseChange k, jM_lat Zr x.m.z.pins x.m.intersectionNumber_baseChange k,
      mjLat_sub Zr x.m.z.pins x.m.intersectionNumber_baseChange k, MjModel.jM_metric_all Zr x.m.intersectionNumber_baseChange k⟩
  let Xd : DivX (w.st x.o.Z).toD7 := GlobalTheory.provisionalDivX (w.st x.o.Z).toD7 G Y
    (fun p _ => (GlobalTheory.WittFracComplex.nonempty_ringHom_complex p).some)
    (fun p _ r => (GlobalTheory.nonempty_admissibleModel _ p _ (max r 2) 1 (by omega)).some) Fm
  have hMj := mjHTie_of_eq Zr Xd rfl (HEq.refl (jM Zr))
  have hIdx : IdxDefs (w.st x.o.Z).toD7 Xd := (P.q.num x.o.η x.o.hη x.o.V x.o.S x.o.N x.o.G).idx Xd
  have hT := GlobalTheory.T.numbers_eq_concreteNumbers_at_baseLevel _ _ _ _ _ _ _ x.m.z.R x.m.z.F x.m.z.cG x.s.p0 x.r.Y Zr Xd _ x.m.z.pins x.m.intersectionNumber_baseChange hMj hIdx
  have hv' : v ∉ x.m.z.W1 (F0K K.s (w.D x.o.Z)) := hW ▸ hv
  have h0 : x.r.Y.tup (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A.μ0 = (w.D x.o.Z).what₂.mu0 := by
    rw [x.r.tup]; exact x.m.y.tup0
  have hIj := hT.Ij
  have hjw := hT.jw
  have hv2 := fun (i : Fin (w.st x.o.Z).toD7.R.m) (w' : HeightOneSpectrum (𝓞 (w.st x.o.Z).toD7.what₂.LL))
      (hw' : w' ∈ ({(w.st x.o.Z).toD7.plEq v, Formalism.DivisionValues.conjPl ((w.st x.o.Z).toD7.plEq v)} : Set _)) =>
    not_or.1 (fun h => hv' ⟨i, w', hw', h⟩)
  have hm : (w.st x.o.Z).toD7.R.m = B.R.m := rfl
  obtain ⟨i, rfl⟩ : ∃ i : Fin (w.st x.o.Z).toD7.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  rw [← h0]
  have hp : (w.st x.o.Z).toD7.plEq v ∈ ({(w.st x.o.Z).toD7.plEq v, Formalism.DivisionValues.conjPl ((w.st x.o.Z).toD7.plEq v)} : Set _) :=
    Set.mem_insert _ _
  refine ⟨?_, ?_⟩
  · exact (hIj i _ v).trans (not_not.1 (hv2 i _ hp).1)
  · exact (hjw i _ v).trans (not_not.1 (not_or.1 (hv2 i _ hp).2).1)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndicesPairingLengthsVanishOffTwistedPlacesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indices_pairingLengths_vanish_off_twistedPlaces : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P), P.Wt = x.m.z.W1 (F0K K.s (w.D x.o.Z)) → ∀ v, v ∉ P.Wt → ∀ j, 1 ≤ j → j ≤ B.R.m →
      (w.D x.o.Z).what₂.Ij (w.D x.o.Z).what₂.mu0 j v = 0 ∧ (w.D x.o.Z).what₂.jw (w.D x.o.Z).what₂.mu0 j v = 0 := by
  first | exact @GlobalTheory.Mem.R3.Rw.St.idx_zero_off_twisted_anyEta | exact GlobalTheory.Mem.R3.Rw.St.idx_zero_off_twisted_anyEta | (intros; apply GlobalTheory.Mem.R3.Rw.St.idx_zero_off_twisted_anyEta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelMapExtensionStatement
section
open NumberField Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj GlobalTheory.OneMapTuples
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_map_extension : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → IoExt R → ∀ (i : Fin D.R.m) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E) (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W) (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W), Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∃ (lam : AutQ (Wc D i) → ℂ) (z : G), (∀ q, lam q ≠ 0) ∧ ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), D.what₂.embLL.toRatAlgHom.fieldRange ≤ O.c'.F → O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → O.lev = lev → CoefficientBaseChange R i O.jL (inC O.c') (c0L i) O.c0' → ∀ c0 : ℂ, XiConst O (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) c0 → PtIdent O (κ i) lam z c0 := by
  first | exact @GlobalTheory.PtId.point_identity | exact GlobalTheory.PtId.point_identity | (intros; apply GlobalTheory.PtId.point_identity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftScalarEqLabelScalar
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.LamLab

theorem adj_eig {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (θ : X →ₗ[ℂ] Y) (c : ℝ) (x₀ : X)
    (h : ∀ x', ⟪θ x₀, θ x'⟫_ℂ = (c : ℂ) * ⟪x₀, x'⟫_ℂ) : θ (LinearMap.adjoint θ (θ x₀)) = (c : ℂ) • θ x₀ := by
  have ha : LinearMap.adjoint θ (θ x₀) = (c : ℂ) • x₀ := by
    refine ext_inner_right ℂ fun x' => ?_
    rw [LinearMap.adjoint_inner_left, h, inner_smul_left, Complex.conj_ofReal]
  rw [ha, map_smul]

theorem eigenvalue_eq_of_label : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (σ : D.what₂.FT) (p : A3.fam3.base3.Ix) (i : Fin D.R.m) (t : T), HasLab Y σ p → (Y.tup t = D.what₂.mu0 ∨ ∃ w, Y.tup t = D.what₂.muAt w) → D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ → D.what₂.lamP (Y.tup t) ((i : ℕ) + 1) σ = (s0Of R F).lam i t p A3.fam3.base3.v0 := by
  intro h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hD σ p i t hL hU hne
  refine Y.tied.lift.lamP (Y.tup t) hU i σ _ hne fun y hy => ?_
  set θ := D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) with hθ
  obtain ⟨x, rfl⟩ := GlobalTheory.T.liftThetaMap_surjective_onto_cuspForms_usedTuple h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t hU y
  set K := (LinearMap.ker θ)ᗮ
  have hx0 : x - K.starProjection x ∈ LinearMap.ker θ := by
    have := K.sub_starProjection_mem_orthogonal x
    rwa [Submodule.orthogonal_orthogonal] at this
  have he : θ (K.starProjection x) = θ x := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hx0; exact hx0.symm
  have hW : Y.mj.eW i (θ (K.starProjection x)) ∈ R.Wp3 i p := by
    rw [he]; exact hL.1 i ⟨θ x, hy, rfl⟩
  have key := GlobalTheory.T.liftThetaMap_inner_eq_lambda_labelPart_baseLevel h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t p hU (K.starProjection x)
    (K.starProjection_apply_mem x) hW
  have := adj_eig θ (R.lam3 i t p A3.A.v0) _ key
  rw [he] at this
  exact this

end GlobalTheory.Mem.R3.LamLab
end

