import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsLevDatHalfLatInd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.NX (ExpSet CoefLat)
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Tow

variable {D : D7}

abbrev lat (E : ExpSet D) : AddSubgroup (WO E.V E.W) := latO E.V E.W E.ΛV E.ΛW fun _ => True

def VacE (E : ExpSet D) : Prop := VacPair E.ψ E.θ E.V E.W E.χV E.χW E.om E.ΛV E.ΛW E.sW E.f₀

def trSpan (E : ExpSet D) (e : AE D) (M : ℕ) (O : Subring ℂ) : Submodule O (WO E.V E.W → ℂ) :=
  Submodule.span O {f | ∃ y : WO E.V E.W, IsHalf e y ∧ M • y ∈ lat E ∧ f = heisO E.ψ E.V E.W y E.f₀}

def stdFock (E : ExpSet D) (f : WO E.V E.W → ℂ) : MvPolynomial (FVar D E.W.rank E.V.rank) ℂ →ₗ[ℂ] (WO E.V E.W → ℂ) :=
  pureTensorO E.ψ E.θ E.V E.W (fun _ => 1) E.sW (fun _ => 1) E.BW f

def badN (D : D7) : ℕ := D.host.QS * D.host.q * Ideal.absNorm D.host.ccK

def ChiGood (E : ExpSet D) : Prop :=
  ∃ χ : Formalism.L2.Host.HChar D.host.E, ChrEq E.χW χ ∧
    (∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((modN E 1 : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal → χ.UnrAt Q) ∧
    ∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k, χ.resFin (Q.under (𝓞 D.host.F)) k = 1

def CoefRing (E : ExpSet D) (O : Subring ℂ) : Prop :=
  (∀ k : ℕ, Nat.Coprime k E.l → (k : ℂ)⁻¹ ∈ O) ∧
    ∀ χ : Formalism.L2.Host.HChar D.host.E, ChrEq E.χW χ → ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      ((modN E 1 * E.l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → GlobalTheory.IdemSupport.cP P ≠ P →
        ((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ) ∈ O ∧
          (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ))⁻¹ ∈ O

def PlaceIn (Λ : Subring ℂ) (F : IntermediateField ℚ ℂ) [NumberField F] (la : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ x : F, la.valuation F x ≤ 1 ↔ (x : ℂ) ∈ Λ

def lamOf {O : Type} [CommRing O] [IsDomain O] (e : FractionRing O →+* ℂ) : Subring ℂ :=
  (e.comp (algebraMap O (FractionRing O))).range

section Core

variable (T : CoreJ D) (j : ℕ) (E : ExpSet D) (hW : T.V j T.σ₀ = E.W) (hr : E.W.rank = D.R.r) (w : WeightFamilies.Wt D j)

def iotaE : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin E.W.rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j

def muE (dd : GA D E.W → ℂ) : GA D E.W → ℂ := fun g => castDict hW (T.mu j T.σ₀) g * dd g

structure Setg (ph : ℂ) (dd : GA D E.W → ℂ) : Prop where
  laws : LawsJ T
  inR : InR D j
  odd : Odd D.R.r
  wn : w.n = E.V.rank
  dom : Dom (wtA w) w.n
  last : w.LastPos
  lastD : LastPos (T.Q.Dw j) (wtA w)
  big : 8 * D.R.f * D.R.r + 4 ≤ w.n
  vac : VacE E
  chi : ChiGood E
  frame : FrameTie (T.U j T.σ₀) E.W hr (T.x₀ j T.σ₀) E.sW E.BW
  lp : E.l.Prime
  good : T.Q.l.GoodAt E.l
  lev : T.Q.l.M = E.gp 0 * E.gp 1
  gp : ∀ a, (E.gp a).Prime
  gne : E.gp 0 ≠ E.gp 1
  pde : ∀ a, (E.pde a).Prime
  cop : Nat.Coprime T.Q.l.M (badN D)
  aux : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsAuxiliarySplitSquarefreeLevel D T.Q.l.M (E.pde 0 * E.pde 1)
  pg : ∀ PP ∈ E.Pg, T.Q.l.Mb ≤ PP.asIdeal
  pd : ∀ PP ∈ E.Pd, ((E.pde 0 * E.pde 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal
  pdHalf : ∀ PP ∈ E.Pd, ∀ PP' ∈ E.Pd, (∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.E) ∈ PP.asIdeal ∧ (p : 𝓞 D.host.E) ∈ PP'.asIdeal) →
    PP.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = PP'.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))
  ddc : IsCompFn E 1 dd
  ddfin : ∃ m : ℕ, 0 < m ∧ ∀ g, dd g ^ m = 1
  mu : MuVal E.W E.χV (muE T j E hW dd)
  muK : ∀ k ∈ T.Kf j T.σ₀, ∀ h, T.mu j T.σ₀ (h * k) = T.mu j T.σ₀ h
  cc : CcIs E.θ E.V E.W hr (T.U j T.σ₀) (castDict hW (T.dict j T.σ₀)) (muE T j E hW dd) (T.x₀ j T.σ₀) E.om E.f₀
    fun k => ph * T.cE j T.σ₀ k
  full : ∀ f ∈ T.cuspA j (wtA w) w.n, ∃ a : ℕ, a ≠ 0 ∧ ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F),
    GlobalTheory.GoodPts.BddAll (T.Q.Xo j) T.Q.c la 1 ((a : T.Q.c.F) • f)

structure IsTw (ph : ℂ) (dd : GA D E.W → ℂ) (N : ℕ) (C : Cover T j T.σ₀) : Prop where
  unif : C.IsUnif
  emb : C.σ₂ = inC C.d.c₂
  pd : C.d.pd = E.pde 0 * E.pde 1 * N
  half : ∀ PP ∈ E.Pd, C.d.I ≤ PP.asIdeal
  curve : GlobalTheory.CompRat.CurveOver T.Q.H C.d.c₂.F C.d.l₂.M
  dict : IsDict C.U₂ E.W hr (castDict hW C.dict₂) (iotaE T j E hr) (T.x₀ j T.σ₀)
  frame : FrameTie C.U₂ E.W hr (T.x₀ j T.σ₀) E.sW E.BW
  cc : CcIs E.θ E.V E.W hr C.U₂ (castDict hW C.dict₂) (muE T j E hW dd) (T.x₀ j T.σ₀) E.om E.f₀ fun k => ph * C.cc₂ k

def ratSet (C : Cover T j T.σ₀) : Set (GA D E.W → ℂ) := castDict hW '' C.ratForms (wtA w) w.n

def intSet (C : Cover T j T.σ₀) (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) : Set (GA D E.W → ℂ) :=
  castDict hW '' C.intForms (wtA w) w.n {la}

def baseSet : Set (GA D E.W → ℂ) :=
  {F | ∃ f ∈ T.cuspA j (wtA w) w.n, F = castDict hW (T.phiJ j T.σ₀ (wtA w) f)}

def baseIntSet : Set (GA D E.W → ℂ) :=
  {F | ∃ f ∈ T.cuspA j (wtA w) w.n, (∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), GlobalTheory.GoodPts.BddAll (T.Q.Xo j) T.Q.c la 1 f) ∧
    F = castDict hW (T.phiJ j T.σ₀ (wtA w) f)}

abbrev harmSet : Set (MvPolynomial (LtN (T.Q.Dw j) E.V.rank) ℂ) :=
  HHa (T.Q.Dw j).mult E.V.rank ℂ ComplexEmbedding.conjugate (InPsi T.Q.H) fun τ i => wtA w (τ, i)

variable (lt : LtN (T.Q.Dw j) E.V.rank ≃ FVar D E.W.rank E.V.rank)

def ReadsAs (P : MvPolynomial (FVar D E.W.rank E.V.rank) ℂ) (Q : MvPolynomial (LtN (T.Q.Dw j) E.V.rank) ℂ) : Prop :=
  Q ∈ harmSet T j E w ∧ ∀ f, IsThetaFunO E.ψ E.V E.W f → E.fock f P = stdFock E f (MvPolynomial.rename lt Q)

variable {O : Type} [CommRing O] (C : CoefLat E O)

def CoefRat (ph : ℂ) (L : Subfield ℂ) : Prop :=
  ∀ P : C.Cf, ∃ Q, ReadsAs T j E w lt (C.rd P) Q ∧ ∀ mo, ph * Q.coeff mo ∈ L

def CoefInt (ph : ℂ) (Λ : Subring ℂ) : Prop :=
  ∃ c : ℕ, ∀ s ∈ GfC E.V, AdaptL E s → ∀ P ∈ C.LL s, ∃ Q, ReadsAs T j E w lt (C.rd P) Q ∧
    ∀ mo, (E.l : ℂ) ^ c * ph * Q.coeff mo ∈ Λ

def FieldIn (dd : GA D E.W → ℂ) (L : Subfield ℂ) : Prop :=
  NumberField L ∧ (∀ x ∈ T.Q.c.F, x ∈ L) ∧ GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (modN E 1) L ∧ (∀ g, dd g ∈ L) ∧ CoefRing E L.toSubring

end Core

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}

structure ReadsAt {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)
    (E : ExpSet D) : Prop where
  V : E.V = Vc D i
  W : E.W = Wc D i
  ψ : E.ψ = R.ψ
  θ : E.θ = R.θ
  sW : HEq E.sW (cart (R.MW i (sg0 D A)))
  BW : HEq E.BW (onb (R.MW i (sg0 D A)))
  ΛV : HEq E.ΛV (R.ΛV i)
  ΛW : HEq E.ΛW (R.ΛW i)
  χV : E.χV = (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1
  χW : E.χW = (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2
  om : HEq E.om (R.ωP i t)
  f₀ : HEq E.f₀ (R.vacP i)
  gp : E.gp = D.host.g
  Pg : E.Pg = R.Pg
  Pd : E.Pd = R.Q t
  pde : E.pde = ![D.host.pde, D.host.pde']

def PhaseIs (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m)
    (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i) (w : WeightFamilies.Wt D ((i : ℕ) + 1)) (ph : ℂ) : Prop :=
  ‖ph‖ = 1 ∧ ∃ cc : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ,
    CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) T.σ₀) (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀))
      (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) (T.x₀ ((i : ℕ) + 1) T.σ₀) (R.ωP i A.μ0) (R.vacP i) cc ∧
    ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA w) w.n, ∀ k x,
      cc k * rdU (T.U ((i : ℕ) + 1) T.σ₀) f k x = ph * T.cE ((i : ℕ) + 1) T.σ₀ k * rdU (T.U ((i : ℕ) + 1) T.σ₀) f k x

end Real

end GlobalTheory.Tow

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.GenInhabited
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Asc.FamilyModel

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.ConjWeil

variable {D : D7}

theorem cjOm_apply {S T : HSp D} (om : Om (negSp S) T) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    cjOm om p f = cj id (om (negGA S p.1, p.2) (cj id f)) := rfl

theorem negGA_mem_GQ (V : HSp D) (γ : GA D V) (h : γ ∈ GQ V) : negGA V γ ∈ GQ (negSp V) := by
  unfold GQ HFinIn HFin at *
  erw [Subgroup.mem_subgroupOf] at h ⊢
  convert h using 2 <;> first | rfl | exact (UJ_neg _ _)

theorem weil_cjOm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : Om (negSp S) T) (hw : IsWeilDatumO ψ (negSp S) T χS χT om) :
    IsWeilDatumO ψ S T χS⁻¹ χT⁻¹ (cjOm om) := by
  have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hw.std S T
  have thS : ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f ↔ IsThetaFunO ψ (negSp S) T (cj id f) := fun f => (I.1 f).2.symm
  have thS' : ∀ f : WO S T → ℂ, IsThetaFunO ψ (negSp S) T f ↔ IsThetaFunO ψ S T (cj id f) := fun f => by
    have := (I.1 (cj id f)).2
    rwa [cj_id_cj_id] at this
  have hzS : ∀ (w : WO S T) (f : WO S T → ℂ),
      heisO ψ S T w f = cj id (heisO ψ (negSp S) T w (cj id f)) := fun w f => by
    rw [(I.2 w f).2, cj_id_cj_id]
  refine
    { std := hw.std
      hecS := hecke_inv hw.hecS
      hecT := hecke_inv hw.hecT
      resS := resEta_inv hw.resS
      resT := resEta_inv hw.resT
      om_pres := ?_
      om_heis := ?_
      om_aut := ?_
      om_cont := ?_
      om_unit := ?_
      om_split := ?_ }
  · intro p f hf
    rw [cjOm_apply, thS, cj_id_cj_id]
    exact hw.om_pres _ _ ((thS f).1 hf)
  · intro g h w₀ f hf
    rw [cjOm_apply, cjOm_apply, hzS w₀ f, cj_id_cj_id]
    erw [hw.om_heis _ _ _ _ ((thS f).1 hf)]
    rw [hzS _ (cj id _), cj_id_cj_id, actO_negS, MulEquiv.symm_apply_apply]
  · intro γ hγ γ' hγ' f hf
    rw [cjOm_apply]
    show starRingEnd ℂ (om (negGA S γ, γ') (cj id f) 0) = f 0
    rw [hw.om_aut _ (negGA_mem_GQ S γ hγ) γ' hγ' _ ((thS f).1 hf)]
    show starRingEnd ℂ (starRingEnd ℂ (f 0)) = f 0
    simp
  · intro f hf w
    have hc := hw.om_cont _ ((thS f).1 hf) w
    simp only [cjOm_apply]
    exact Complex.continuous_conj.comp
      (hc.comp (((continuous_negGA S).comp continuous_fst).prodMk continuous_snd))
  · intro μ 𝓕 hμ hF p f hf
    have hu := hw.om_unit μ 𝓕 hμ hF (negGA S p.1, p.2) (cj id f) ((thS f).1 hf)
    simp only [cjOm_apply, cj_id_apply, enorm_conj] at hu ⊢
    exact hu
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := hw.om_split e he (negGA S g) h
      (by unfold SuppAt; rw [mt_negGA]; exact hg) hh x y (by unfold IsDetAt; rw [mt_negGA]; exact hx) hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun f => starRingEnd ℂ (ℓ (cj id f))
        map_add' := fun a b => by
          have : cj id (a + b) = cj id a + cj id b := by funext z; simp [cj_id_apply]
          rw [this, map_add, map_add]
        map_smul' := fun c a => by
          have : cj id (c • a) = starRingEnd ℂ c • cj id a := by funext z; simp [cj_id_apply]
          rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj]; rfl }
    have h1 : starRingEnd ℂ (ℓ (cj id (om (negGA S g, h) (cj id f)))) =
        (r : ℂ) * (splitFacO χS χT x y : ℂ) * starRingEnd ℂ (ℓ (cj id (cj id f))) :=
      H ℓ' (fun u hu f' hf' => by
        show starRingEnd ℂ (ℓ (cj id (heisO ψ (negSp S) T u f'))) = starRingEnd ℂ (ℓ (cj id f'))
        have e1 := hzS u (cj id f')
        rw [cj_id_cj_id] at e1
        rw [← e1, hℓ u hu (cj id f') ((thS' f').1 hf')]) (cj id f) ((thS f).1 hf)
    rw [cj_id_cj_id, ← cjOm_apply om (g, h) f] at h1
    rw [splitFacO_inv]
    have h2 := congrArg (starRingEnd ℂ) h1
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at h2
    exact h2

theorem vac_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (Γ : AddSubgroup (WO S T)) (f : WO S T → ℂ) :
    VacG ψ (negSp S) T Γ f ↔ VacG ψ S T Γ (star f) := by
  have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S T
  have e0 : star f = cj id f := rfl
  have th : IsThetaFunO ψ (negSp S) T f ↔ IsThetaFunO ψ S T (cj id f) := by
    have := (I.1 (cj id f)).2
    rwa [cj_id_cj_id] at this
  have hz : ∀ w : WO S T, heisO ψ (negSp S) T w f = f ↔ heisO ψ S T w (cj id f) = cj id f := fun w => by
    have := (I.2 w (cj id f)).2
    rw [cj_id_cj_id] at this
    rw [this]
    exact ⟨fun h => by have := congrArg (cj id) h; rwa [cj_id_cj_id] at this, fun h => by rw [h, cj_id_cj_id]⟩
  rw [e0]
  unfold VacG IsLatVac
  simp only [th, hz]

theorem part_succ {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : GlobalTheory.FunObj.Vol G) (ρ Φ u) (i : ℕ)
    (hi : i < D.R.m) : part W M ρ Φ u (i + 1) hi = liftA W M (.right i 0) (W.datum ρ Φ ⟨i, hi⟩) (part W M ρ Φ u i hi.le) := rfl

theorem part_congr {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : GlobalTheory.FunObj.Vol G) (ρ Φ ρ' Φ' u)
    (i : ℕ) (hi : i ≤ D.R.m) (h : ∀ j : Fin D.R.m, j.1 < i → ρ j = ρ' j ∧ Φ j = Φ' j) :
    part W M ρ Φ u i hi = part W M ρ' Φ' u i hi := by
  unfold part
  congr 2
  funext j
  have := h (Fin.castLE hi j) j.2
  unfold GridData.Weil.datum
  rw [this.1, this.2]

theorem conjRead : ConjRead := by
  intro D hq T L μ0 hL sc G W M hM i hi
  have r1 : (G.pS (.chi i 0)).rank = rankV D (i + 1) 0 := (node_isV G hL (X := .grid (i + 1) 0) ⟨hi, Nat.zero_le _⟩).rank
  have r0 : (G.pT (.chi i 0)).rank = rankV D i 0 := (node_isV G hL (X := .grid i 0) ⟨hi.le, Nat.zero_le _⟩).rank
  have e1 := even_rankV D (i + 1) 0
  have e0 := even_rankV D i 0
  refine ⟨weil_cjOm _ _ _ _ _ _ (W.om_is (.chi i 0) ⟨hi, Nat.zero_le _⟩), ?_, fun ho => ?_, fun he => ?_, fun f => ?_,
    fun v f Ψ => ?_, fun ρ Φ u => ?_, fun ρ Φ ρ' Φ' u h => part_congr W M ρ Φ ρ' Φ' u i hi.le h, (hM.row i hi.le).haar_fund⟩
  · have := weil_cjOm _ _ _ _ _ _ (W.om_is (.core i) hi)
    rwa [(G.chr_core hi).1, (G.chr_core hi).2] at this
  · rw [GridData.chrS, GridData.chrT, r1, r0, Formalism.IndefR.Lift.attChr, Formalism.IndefR.Lift.attChr,
      if_pos (Nat.not_even_iff_odd.1 (by rw [e1]; simpa [Nat.odd_add_one] using ho)),
      if_neg (Nat.not_odd_iff_even.2 (e0.2 (by simpa using ho)))]
    exact ⟨by simp [GridData.chr, mul_comm], rfl⟩
  · rw [GridData.chrS, GridData.chrT, r1, r0, Formalism.IndefR.Lift.attChr, Formalism.IndefR.Lift.attChr,
      if_pos (Nat.not_even_iff_odd.1 (by rw [e0]; simpa using he)),
      if_neg (Nat.not_odd_iff_even.2 (e1.2 (by simpa [Nat.odd_add_one] using he)))]
    exact ⟨by simp [GridData.chr, mul_comm], rfl⟩
  · exact vac_star W.ψ_std (G.V (.core (i + 1))) (G.V (.core i)) (latCore G i) f
  · funext g
    rw [liftT_apply, Pi.star_apply, dn, Complex.star_def, ← integral_conj]
    refine integral_congr_ae (.of_forall fun h => ?_)
    simp only [map_mul, cjOm_apply]
    congr 1
    exact congrArg (fun z => starRingEnd ℂ (W.om (.core i) (negGA _ h, g) z 0)) (cj_id_cj_id f).symm
  · funext g
    rw [liftS_apply, Pi.star_apply, part_succ, liftA_apply, Complex.star_def, ← integral_conj]
    refine integral_congr_ae (.of_forall fun h => ?_)
    simp only [map_mul, cjOm_apply]
    congr 1
    exact congrArg (fun z => starRingEnd ℂ (W.om (.chi i 0) (negGA _ g, h) z 0)) (cj_id_cj_id _).symm

theorem partFixed (h1 : DepFixed) (h2 : DatumDep) : PartFixed := by
  intro D hq T L μ0 hL sc G W M hM ρ Φ u i h k hk g
  rw [part_succ W M ρ Φ u i h, liftA_apply, liftA_apply]
  refine integral_congr_ae (.of_forall fun x => ?_)
  have := h1 D hq T L μ0 hL sc G W M hM i h (.chi i 0) (Or.inl rfl) _ (h2 D hq T L μ0 hL sc G W M hM ρ Φ ⟨i, h⟩) 1 (one_mem _) k hk
  have e : W.kerA (.right i 0) (W.datum ρ Φ ⟨i, h⟩) x (g * k) = W.kerA (.right i 0) (W.datum ρ Φ ⟨i, h⟩) x g := by
    show W.om (.chi i 0) (negGA _ (g * k), x) _ 0 = W.om (.chi i 0) (negGA _ g, x) _ 0
    have e2 : ((negGA _ (g * k), x) : GA D (G.pS (.chi i 0)) × GA D (G.pT (.chi i 0))) = (negGA _ g, x) * (negGA _ k, 1) := by
      rw [map_mul, Prod.mk_mul_mk, mul_one]
    rw [e2, map_mul, Module.End.mul_apply]
    exact congrArg (fun z => W.om (.chi i 0) (negGA _ g, x) z 0) this
  simp only [e]

theorem exists_gen {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (B : BesLev D ρ) {W W₀ : HSp D}
    (dW : HypDec W W₀ ρ) (n : ℕ) (g : Fin n → GA D B.V₀) :
    ∃ a : Gen ψ B.V B.V₀ W ρ (Fin n), a.Is ∧ a.g = g ∧ a.m = Measure.count ∧ a.x₀ = dW.e ∧
      ∀ y, ∀ x ∈ flagN a.d, ‖a.Th y x‖ = 1 := by
  obtain ⟨χV, χW, om, hom⟩ := Inhab.exists_weil_pair hψ B.V W
  obtain ⟨vS⟩ := Inhab.nonempty_volM D W.rank ρ
  obtain ⟨vb⟩ := Inhab.nonempty_volM D ρ B.V₀.rank
  obtain ⟨vU⟩ := Inhab.nonempty_volU D ρ
  obtain ⟨vW⟩ := Inhab.nonempty_vol W
  have hg : gramQ W dW.e = 0 := by rw [gramQ, ← Matrix.mul_assoc]; exact dW.ee
  have hT := CutChar.conjBessel_isTh D ψ hψ ρ B W dW.e hg
  have hn : ∀ x, ‖star (psiBes ψ B.d 1 (vecB B.o B.ζ) x)‖ = 1 := fun x => by
    rw [norm_star, psiBes, psiE]; exact hψ.1.2.1 _
  refine ⟨⟨B.d, χV, χW, om, vS, B.vN, vb, vU, vW, dW.e, Measure.count, g, fun _ x => star (psiBes ψ B.d 1 (vecB B.o B.ζ) x)⟩,
    ⟨hom, ⟨(isIsoSub_e dW).1, fun u _ => ?_⟩, inferInstanceAs (SFinite Measure.count), continuous_of_discreteTopology, fun _ => hT,
      hT.cont.comp continuous_snd, fun _ => 1, measurable_const, fun _ x _ => (hn x).le, fun k => Integrable.of_finite⟩,
    rfl, rfl, rfl, fun _ x _ => hn x⟩
  show adj u.1 ⬝ ((rat (gramQ W dW.e) : Mx D ρ ρ) ⬝ u.1) = rat (gramQ W dW.e)
  rw [hg, rat_zero, Matrix.zero_mul, Matrix.mul_zero]

theorem gen_inhabited (D : D7) : ∃ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (a : Gen ψ V V₀ W 1 (Fin 2)),
    a.Is ∧ V₀.rank = 2 ∧ W.rank = 3 ∧ a.m = Measure.count ∧ ∀ y, ∀ x ∈ flagN a.d, ‖a.Th y x‖ = 1 := by
  obtain ⟨⟨ψ, hψ⟩, -⟩ := Inhab.exists_chain D
  obtain ⟨a, h1, -, h2, -, h3⟩ := exists_gen hψ (Inhab.besPlane (GlobalTheory.RegSW.Model.hypFour D) one_ne_zero) (hypDecThree D) 2 fun _ => 1
  exact ⟨ψ, _, _, _, a, h1, rfl, rfl, h2, h3⟩

theorem lhs_count {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ n : ℕ} (a : Gen ψ V V₀ W ρ (Fin n)) (h : a.m = Measure.count) (G Φ) :
    a.lhs G Φ = ∑ y, ∫ x in a.vN.𝓝, a.Th y x.1 * liftS a.om a.vW.μ a.vW.𝓕 G Φ (x.1 * a.d.emb0 (a.g y)) ∂a.vN.ν := by
  rw [Gen.lhs, h, integral_count]

theorem strip_stable (W : HSp D) (R : Subgroup (GA D W)) (C : Set (GA D W)) {h r b : GA D W} (hh : h ∈ strip W R C) (hr : r ∈ R)
    (hb : b ∈ GfC W) : r * h * b ∈ strip W R C := by
  obtain ⟨r', hr', c, hc, b', hb', rfl⟩ := hh
  exact ⟨r * r', mul_mem hr hr', c, hc, b' * b, mul_mem hb' hb, by group⟩

theorem top_of_rungs (h0 : Rung0) (hB : RungB) (hJ : RungJ) :
    OnTower fun {_} _ _ _ {G} W M v F Ψ u _ => per0 G M (Ψ 0) u ≠ 0 → ∀ k h, NZB W M v F Ψ u k h := by
  intro D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu hp k
  induction k with
  | zero => exact fun h => hB D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu 0 h (h0 D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu hp h)
  | succ k ih =>
    exact fun h => hB D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu _ h
      (hJ D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu k h (by omega) (ih (by omega)))

theorem not_nzb {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : GlobalTheory.FunObj.Vol G) (v : CoreVol G)
    (F : Frames G) (u k h) : ¬ NZB W M v F (fun _ => 0) u k h := by
  rintro ⟨ρ, Φ, hne⟩
  exact hne (by simp [BesL.per, GlobalTheory.MixPer.besPer, GlobalTheory.MixPer.besFun])

theorem not_nzj {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : GlobalTheory.FunObj.Vol G) (v : CoreVol G)
    (F : Frames G) (u ΓL k h) : ¬ NZJ W M v F (fun _ => 0) u ΓL k h := by
  rintro ⟨_, _, -, ρ, Φ, Φ₀, -, hne⟩
  exact hne (by simp [JacL.per, fjSrc, fjSrcFun])

end GlobalTheory.Asc.FamilyModel

end
end

