import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1987
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0069
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0054
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0057
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmegaField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEmbeddingIdealLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1658
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2065
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0156
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2064
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelUnitValues
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.SerOne

open GlobalTheory.ClassScalarValue GlobalTheory.PtId

theorem guard_of_splitOffBad {D : D7} (V : HSp D) (hg : V.gram = 1) (hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank)
    {H : Geo.Tor.Host D.host.E} (l : Geo.Tor.Level H) {bad : ℕ} (h2 : 2 ∣ bad) (hM : l.M ∣ bad) {h : GA D V}
    (hs : SplitOffBad V bad h) : GlobalTheory.ClassScalarCompare.Guard H bad (Bridge.hLat V (fin V h)) := by
  obtain ⟨e, e1, e2, e3, e4⟩ := (GlobalTheory.RepsCompare.suppSplitOff_iff _ _ _).1
    (GlobalTheory.RepsCompare.suppSplitOff_of_splitOffBad _ _ _ hs)
  have hs' : GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) (bad * l.M) (finHom V h).1 := by
    refine ⟨e, e1, e2, fun v hv => ⟨(e3 v hv).1, fun hm => (e3 v hv).2 ?_⟩, e4⟩
    rw [Nat.cast_mul] at hm
    refine (v.isPrime.mem_or_mem hm).elim id fun h => ?_
    obtain ⟨u, rfl⟩ := hM
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h
  obtain ⟨-, c1, c2, -, -, c5⟩ := GlobalTheory.SplitReps.exists_conjLat V hg hL H l bad h2 h hs'
  have g := GlobalTheory.ClassScalarCompare.guard_conjLat (H := H)
    (L := (GlobalTheory.UnRep.FullReps.conjLat H (Bridge.hLat V (fin V h))).La) ⟨c1, c2, c5⟩
  have e2 : (GlobalTheory.ClassScalarCompare.conjLat (GlobalTheory.UnRep.FullReps.conjLat H (Bridge.hLat V (fin V h))).La).La =
    Bridge.hLat V (fin V h) := GlobalTheory.ClassScalarCompare.conjLat_conjLat _
  rwa [e2] at g

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

set_option maxHeartbeats 800000 in

theorem lattice_scalar_value (hC : GlobalTheory.Hk3.Core R F) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Tp tup)
    (hO : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) (t : Tp) (h : GA D (Vc D i)) (e : AE D)
    (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ) (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((O.bad t : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) (hs : SuppAt e (Vc D i) h) (hy : IsDetAt e (Vc D i) h y)
    (hbad : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q (tup t) → ((O.bad t : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (Λ : GenLat D.host.E (Vc D i).rank) (N M : ℕ)
    (hcj : Λ = GlobalTheory.ClassScalarCompare.conjLat (Bridge.hLat (Vc D i) (fin (Vc D i) h)))
    (g : GlobalTheory.ClassScalarCompare.Guard T.Q.H (O.bad t) (Bridge.hLat (Vc D i) (fin (Vc D i) h))) (r4 : Λ.LevOK N M) :
    inC O.c' (O.epF t (Bridge.hLat (Vc D i) (fin (Vc D i) h)) * ((Λ.mIdx N D.R.r : O.c'.F))⁻¹ * (Λ.zCard N D.R.r : O.c'.F)) =
      (((Lift.chrTh (R.toLevCh.mu (tup t)) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)⁻¹ *
        (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf
          Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ) := by
  have hL := hC.lev
  have hpq : D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q :=
    (hT.laws.unf _ ⟨Nat.le_add_left _ _, i.2⟩ _ T.toCore.good_σ₀).1
  have hbar : (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
    RingHom.ext fun a => RingOfIntegers.ext (T.Q.H.bar_eq a)
  obtain ⟨cc, c0, c1, c2, c3, c4⟩ := exists_ideal (Vc D i) hO.lift.std.1 hO.lift.std.2 h e P y he hs hy (O.bad t) hP _ _
    (chrEq_mul_inv (hL.mu0 i) (hL.xi (tup t)) hL.eta)
    (fun Q hQ x hx => by
      have a1 : (R.C.mu0 i).UnrAt Q := (R.C.isMu0 i).unr Q fun j hj => hQ (by
        obtain ⟨u, hu⟩ := (Finset.dvd_prod_of_mem D.host.g (Finset.mem_univ j)).trans
          ((Fin.prod_univ_two D.host.g).symm ▸ (hO.bad t).2.2.2.2)
        rw [hu, Nat.cast_mul]
        exact Ideal.mul_mem_right _ _ hj)
      have a2 : (R.xiH (tup t)).UnrAt Q := by
        by_contra hn
        rcases (hL.Q_ram (tup t) Q).1 hn with a | ⟨Q', a, a'⟩
        · exact hQ (hbad Q (Or.inr a))
        · rw [(GlobalTheory.IdemSupport.isConjPl_iff _ _).1 a', GlobalTheory.IdemSupport.mem_cP, map_natCast] at hQ
          exact hQ (hbad Q' (Or.inr a))
      rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, a1 x hx, a2 x hx,
        R.C.isEta.unr Q x hx, inv_one, one_mul, one_mul])
    (fun Q hQ x => by
      rw [Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv,
        (R.C.isMu0 i).triv.1, (hL.xi_triv (tup t)).1, R.C.isEta.res.1, Formalism.L2.Host.etaFin, above_eq,
        Finset.card_pair hQ.symm, if_neg (by norm_num), inv_one, one_mul, one_mul])
  rw [← hbar] at c1 c3
  generalize Bridge.hLat (Vc D i) (fin (Vc D i) h) = L at *
  obtain ⟨q, q0, q1, q2⟩ := (hO.ep t).2 L cc g.1 g.2.1 g.2.2 c1 c3
  have hB := (hO.tuple t).B cc c0 c2
  have hi := GlobalTheory.ClassScalarCompare.stdIndex_conjLat L
  rw [← hcj] at hi
  rw [← hpq, ← Nat.cast_pow] at q1
  have := value_calc (x := (((Lift.chrTh (R.toLevCh.mu (tup t)) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)) q0
    (fun h0 => c0 (Ideal.absNorm_eq_zero_iff.1 h0))
    (mIdx_ne_zero Λ D.R.r (fun h0 : N = 0 => by simpa [h0] using r4.1)) q1
  rw [q2, zCard_eq _ _ _ r4.2.2, map_mul, map_mul, map_mul, map_inv₀, map_inv₀, hB, ← c4, map_ratCast,
    map_natCast, map_natCast, ← Nat.cast_pow]
  have hi' : (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index =
      ((L ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index := hi
  rw [← hi'] at this
  exact this

set_option maxHeartbeats 2000000 in

theorem kernel_eq_shortVal (hC : GlobalTheory.Hk3.Core R F) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Unit (fun _ => A.μ0))
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) {ka : ℂ} (hka : IoAt O (v₀ i (sg0 D A)) ka)
    {δ : ℤˣ} (hδ : ClsAt R i (iotaW T i) δ) {cst : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ}
    (hcc : CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0)
      (R.ωP i A.μ0) (R.vacP i) cst)
    (φ : (Fin (Vc D i).rank → LevQc (T.Q.Dw ((i : ℕ) + 1)) T.Q.l) → O.c'.F)
    (hφ : PhiIs R i (inC O.c') A.μ0 (iotaW T i) (Mfr T.Q.l • ⊤) φ) [StarRing (𝓞 D.host.E)]
    (nab : NabV (T.Q.Xo ((i : ℕ) + 1)) O.c') (hnab : IsNab (T.Q.Xo ((i : ℕ) + 1)) O.c' nab)
    (h : GA D (Vc D i)) (La : GenLat D.host.E (Vc D i).rank) (N : ℕ) (hsp : SplitOffBad (Vc D i) (O.bad ()) h)
    (hla : ∀ v, v ∈ La.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) (hN : La.LevOK N T.Q.l.M)
    (hg : GlobalTheory.ClassScalarCompare.Guard T.Q.H (O.bad ()) (Bridge.hLat (Vc D i) (fin (Vc D i) h)))
    (w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (hw : ∀ ρ, (w ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ)
    (xs : VsV D i O.c'.F) (g' : GA D (Wc D i)) (hx : (O.dict g').2 ∈ ((unfO O).X (O.dict g').1).dom) (t : ℂ)
    (ht : letI : Algebra O.c'.F ℂ := (inC O.c').toAlgebra
      ShortValAt (T.Q.Xo ((i : ℕ) + 1)) O.c' nab (phiHat O.c' φ) La 1 N (O.io xs)
        (unC (Formalism.L2.PjFree.Unf.ofPj (unfO O)) (O.dict g').1 ⟨(O.dict g').2, hx⟩) t) :
    thetaKO (R.ωP i A.μ0) h g' (R.ptP i A.μ0 (R.ioP i (PiTensorProduct.tprod ℂ w) (O.c0' xs))) =
      cmpConst D ka δ (degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) * cst (O.dict g').1 * O.mu g' *
        inC O.c' (O.epF () (Bridge.hLat (Vc D i) (fin (Vc D i) h))) * t := by
  letI : Algebra O.c'.F ℂ := (inC O.c').toAlgebra
  have hs : O.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  have hσ : GoodEmb T.Q.c O.s0 := hs ▸ T.toCore.good_σ₀
  have hmod := models_at_record_core D G Pl0 T0 A T R F κ v₀ hC hT i O.s0 hs
  obtain ⟨hemb, -, -, hmk⟩ := dict_cast T hT.laws _ (inR i) O.s0 hσ (Wc D i) O.hV (rank_Wc i)
  obtain ⟨hX, hon, hinv, hp, hrk, hpq, h1, hrt, -, hbas, hD, -⟩ := hmod (O.dict g').1
  have hU : IsUnf (unfO O) := GlobalTheory.OneMapAll.isUnf_unfExt O.hle (inC O.c') (fun _ => rfl) (hT.laws.unf _ (inR i) O.s0 hσ)
  obtain ⟨hx', g, Dc, γ, mk, v, ϑ, κ', B, hat, hsd, hm, hBm, hma, hϑ, hv, hκ, hrd⟩ :=
    exists_point (unfO O) hσ hU h1 hT.laws.pins.2.1.2 R.θ (Vc D i) (Wc D i) (rank_Wc i) O.dict (iotaW T i)
      (T.x₀ ((i : ℕ) + 1) O.s0)
      (fun Wt k => hmk R.θ hC.models.inf (fun k => (hmod k).1) h1 ⟨Wt.g, Wt.e, Wt.F, Wt.ik, Wt.φ, Wt.isom, Wt.pt⟩ k)
      (wtA (κ i)) hD O.mu (R.ωP i A.μ0) (R.vacP i) cst (CcIs.unfBC _ _ _ _ O.hle _ (inC O.c') _ _ _ _ _ _ hcc) g'
  obtain ⟨hγ, hΛ, hfr⟩ := hat
  have hM : 0 < T.Q.l.M := T.Q.l.odd.pos
  obtain ⟨Y, hY⟩ := (DualMark.dual_marking _ _ _ T.Q.l _ _ _ mk _ hsd hm
    (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 (Vc D i).rank N hN.1.pos
  have hcj : La = GlobalTheory.ClassScalarCompare.conjLat (Bridge.hLat (Vc D i) (fin (Vc D i) h)) :=
    congrArg GenLat.mk (Submodule.ext hla)
  have hg' := GlobalTheory.ClassScalarCompare.guard_conjLat hg
  rw [← hcj] at hg'
  have hMb : T.Q.l.M ∣ O.bad () := by
    rw [level_M T.toCore hT.laws.toLawsM]
    exact (hP.bad ()).2.2.2.2
  have hTr : La.TrivAt T.Q.l.M := by
    obtain ⟨k, hk, h2⟩ := hg'.2.1
    exact ⟨k, hk.coprime_dvd_right hMb, h2⟩
  obtain ⟨-, cga, hio⟩ := hP.io
  have hH := mem_HHa_of_span _ _ _ _ _ _ (hio.2.2.1 ▸ LinearMap.mem_range_self O.io xs)
  have hgeo := GlobalTheory.Dict.shortValAt_eq_thP GlobalTheory.ChartFree.chartIndep _ _ _ _ _ O.c' _ g _ Dc.bas Dc.idx Dc.e _ _ _ B Dc.sympl hx hsd
    _ _ Dc.hr Dc.eL hrk hD.2 Dc.dir_eq nab hnab ϑ v κ' hϑ hv hκ mk hm hBm La.La
    ((GlobalTheory.Dict.GenLatCmp.genLat_vset _ _ La.La).2.1 _ N hM hg'.1 hTr hN) N hN Y hY _ _ hH _ 1 t ht
  obtain ⟨vr, hvr⟩ := exists_isVarOf (Vc D i) (Wc D i) (rank_Wc i) _ hX _ Dc.hr
  have hlt := letters_eq_fockVars_core D G Pl0 T0 A T R F κ v₀ hC hT i _ _ O hP _ g Dc vr hX hp hvr
  have hω := hC.thP.ωP i A.μ0
  have hmove : ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f →
      thetaKO (R.ωP i A.μ0) h g' f = thetaKO (R.ωP i A.μ0) h (γ * g') f := fun f hf => by
    have e1 : ((h, γ * g') : GA D (Vc D i) × GA D (Wc D i)) = (1, γ) * (h, g') := by simp
    rw [thetaKO, thetaKO, e1, map_mul]
    exact (hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ f hf)).symm
  rw [hmove _ (hC.thP.pt_theta i A.μ0 _), hka (fun ℓ => vr (Dc.eL ℓ)) hlt w hw A.μ0 xs]
  obtain ⟨hfin, e, Ps, he, hPs, hsupp⟩ := hsp
  obtain ⟨yd, hyd⟩ := exists_isDetAt he (Vc D i) h
  have hhom : (MvPolynomial.rename Dc.eL (MvPolynomial.map (inC O.c') (O.io xs))).IsHomogeneous
      (degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) :=
    ((isHomogeneous_of_rowDeg _ _ _ _ hH.2.2).map _).rename_isHomogeneous
  have hQ : R.Q A.μ0 = ∅ := Finset.eq_empty_of_forall_notMem fun PP hP =>
    (hC.lev.Q_ram A.μ0 PP).2 (Or.inl hP) (by rw [hC.lev.xi_base]; exact fun _ _ => rfl)
  have hhalf : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q A.μ0 → T.Q.l.Mb ≤ PP.asIdeal ∧
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP => by
    obtain ⟨k1, -, k3⟩ := (hP.tuple ()).half
    refine ⟨?_, k3 PP hPP⟩
    rcases hPP with hPP | hPP
    · exact k1.le.trans (Ideal.prod_le_inf.trans (Finset.inf_le hPP))
    · rw [hQ] at hPP
      exact absurd hPP (Finset.notMem_empty _)
  obtain ⟨h₀, J', hR, -⟩ := (hP.tuple ()).reps
  have hcl := hδ A.μ0 T.Q.l (fun x => inC O.c' (φ x)) hφ hhalf hrt g _ _ Dc.hr Dc.bas Dc.idx _ vr hX
    Dc.sympl hon hinv (hbas _) hvr (O.bad ()) N h (γ * g') La mk e Ps yd hR.2.1 he hPs hfin hsupp hyd hla
    hTr hN hma Y (hΛ ▸ hY) v _ (hΛ ▸ hv) (hfr ▸ hrd) _ _ hhom
  have hep := lattice_scalar_value hC hT O hP () h e Ps yd he hPs hsupp hyd hR.2.1 La N _ hcj hg hN
  have hw' : hatC T.Q.l (fun x => inC O.c' (φ x)) = fun q => inC O.c' (phiHat O.c' φ q) := funext fun q =>
    (PairModel.hatC_phiHat O.c' φ q).symm
  rw [← hep, hw', hΛ, MvPolynomial.rename_rename] at hcl
  have hsm : ∀ f, thetaKO (R.ωP i A.μ0) h (γ * g') (ka • f) = ka * thetaKO (R.ωP i A.μ0) h (γ * g') f :=
    fun f => by rw [thetaKO, thetaKO, map_smul]; rfl
  rw [hsm]
  refine (congrArg (fun z => ka * z) hcl).trans ?_
  have e1 := congrArg (thP ((unfO O).X (O.dict g').1) Dc.hr Dc.bas Dc.idx (gphi ((unfO O).X (O.dict g').1) Dc.bas
    (T.Q.H.w0 : D.host.E) La.La ((unfO O).X (O.dict g').1).Λ v (fun q => inC O.c' (phiHat O.c' φ q)) Y)
    (MvPolynomial.rename Dc.eL (MvPolynomial.map (inC O.c') (O.io xs)))) hfr
  refine Eq.trans (congrArg (fun z => ka * (_ * z)) e1.symm) ?_
  refine Eq.trans ?_ (congrArg (fun z => _ * z) hgeo.symm)
  have halg : ∀ s : O.c'.F, algebraMap O.c'.F ℂ s = inC O.c' s := fun _ => rfl
  simp only [cmpConst, halg, map_mul, map_inv₀, map_natCast, map_one, inv_one, one_mul]
  have key : ∀ s c m k e a z n th : ℂ, ka * (s * (c * m * k) * (e * a * z) * n * th) =
      ka * s * c * m * e * (a * n * z * k * th) := fun s c m k e a z n th => by ring
  exact key _ _ _ _ _ _ _ _ _

end GlobalTheory.AdTh.SerOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairEvaluationSelfLinear
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.ThK.EvChangeUniq

def ratInc (F R κ : Type) [Field F] [CommRing R] [Algebra F R] : ((κ → F) × (κ → F)) →ₗ[F] ((κ → R) × (κ → R)) where
  toFun w := (fun i => algebraMap F R (w.1 i), fun i => algebraMap F R (w.2 i))
  map_add' a b := by ext <;> simp
  map_smul' a b := by ext <;> simp [Algebra.smul_def]

theorem ratInc_injective (F R κ : Type) [Field F] [CommRing R] [Algebra F R] (h : Function.Injective (algebraMap F R)) :
    Function.Injective (ratInc F R κ) := by
  intro a b hab
  have h1 := congrArg Prod.fst hab
  have h2 := congrArg Prod.snd hab
  exact Prod.ext (funext fun i => h (congrFun h1 i)) (funext fun i => h (congrFun h2 i))

theorem exists_rat {F R κ V : Type} [Field F] [CommRing R] [Algebra F R] [AddCommGroup V] [Module F V]
    (h : Function.Injective (algebraMap F R)) (c : V →ₗ[F] ((κ → R) × (κ → R)))
    (hc : ∀ x, ∃ w, c x = ratInc F R κ w) :
    ∃ q : V →ₗ[F] ((κ → F) × (κ → F)), ∀ x, ratInc F R κ (q x) = c x := by
  have hmem : ∀ x, c x ∈ LinearMap.range (ratInc F R κ) := fun x => by
    obtain ⟨w, hw⟩ := hc x
    exact ⟨w, hw.symm⟩
  refine ⟨(LinearEquiv.ofInjective _ (ratInc_injective F R κ h)).symm.toLinearMap ∘ₗ c.codRestrict _ hmem, fun x => ?_⟩
  have := LinearEquiv.ofInjective_apply (ratInc F R κ) (h := ratInc_injective F R κ h)
    ((LinearEquiv.ofInjective _ (ratInc_injective F R κ h)).symm (c.codRestrict _ hmem x))
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem exists_lagrangian {F R κ V : Type} [Field F] [CommRing R] [Algebra F R] [AddCommGroup V] [Module F V] [Fintype κ]
    [FiniteDimensional F V] (hV : Module.finrank F V = Fintype.card κ + Fintype.card κ)
    (h : Function.Injective (algebraMap F R)) (c c₁ : V →ₗ[F] ((κ → R) × (κ → R)))
    (hc : ∀ x, ∃ w, c x = ratInc F R κ w) (hc₁ : ∀ x, ∃ w, c₁ x = ratInc F R κ w)
    (hi : Function.Injective c) (hi₁ : Function.Injective c₁)
    (hf : ∀ x y, (c x).1 ⬝ᵥ (c y).2 - (c y).1 ⬝ᵥ (c x).2 = (c₁ x).1 ⬝ᵥ (c₁ y).2 - (c₁ y).1 ⬝ᵥ (c₁ x).2) :
    ∃ L : Submodule F ((κ → F) × (κ → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
      Module.finrank F L = Fintype.card κ ∧ ∀ w ∈ L, ∃ x, ratInc F R κ w = c x ∧ (c₁ x).1 = 0 := by
  obtain ⟨q, hq⟩ := exists_rat h c hc
  obtain ⟨q₁, hq₁⟩ := exists_rat h c₁ hc₁
  have hqi : Function.Injective q := fun a b hab => hi (by rw [← hq, ← hq, hab])
  have hqi₁ : Function.Injective q₁ := fun a b hab => hi₁ (by rw [← hq₁, ← hq₁, hab])
  have hqs : Function.Surjective q₁ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hV])).1 hqi₁
  let K : Submodule F V := LinearMap.ker (LinearMap.fst F _ _ ∘ₗ q₁)
  have hK : Module.finrank F K = Fintype.card κ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.fst F _ _ ∘ₗ q₁)
    have h2 : LinearMap.range (LinearMap.fst F _ _ ∘ₗ q₁) = ⊤ :=
      LinearMap.range_eq_top.2 (Prod.fst_surjective.comp hqs)
    rw [h2, finrank_top, hV, Module.finrank_fintype_fun_eq_card] at h1
    exact Nat.add_left_cancel h1
  have hL : ∀ w ∈ K.map q, ∃ x, ratInc F R κ w = c x ∧ (c₁ x).1 = 0 := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, hq x, ?_⟩
    have hx' : (q₁ x).1 = 0 := hx
    rw [← hq₁]
    funext i
    simp [ratInc, hx']
  refine ⟨K.map q, fun a ha b hb => ?_, ?_, hL⟩
  · obtain ⟨x, hx, hx0⟩ := hL a ha
    obtain ⟨y, hy, hy0⟩ := hL b hb
    have h1 := hf x y
    rw [hx0, hy0, ← hx, ← hy, zero_dotProduct, zero_dotProduct, sub_zero, sub_eq_zero] at h1
    apply h
    simpa [dotProduct, ratInc] using h1
  · rw [← hK]
    exact (Submodule.equivMapOfInjective q hqi K).finrank_eq.symm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def incL (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (n d : ℕ) :
    Matrix (Fin n) (Fin d) E →ₗ[F] Matrix (Fin n) (Fin d) (AE F E) :=
  LinearMap.mapMatrix (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).toLinearMap

theorem incL_injective (n d : ℕ) : Function.Injective (incL F E n d) := by
  intro a b hab
  ext i j
  exact Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F) (congrFun (congrFun hab i) j)

theorem eq_smul_isEv : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (M₁ : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsEv B M M₁ 1 1 ∅ e → ∀ f : Fn F n d →ₗ[ℂ] Fn F n d,
    (∀ (z : Matrix (Fin n) (Fin d) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d), f (M.co.rho B.ψ z Φ) = M₁.co.rho B.ψ z (f Φ)) →
    ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), f Φ = c • e Φ := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ e hM₁ hev f hfh
  have hψ : IsStd B.ψ := hpair.base.std
  have hM : M.IsGood B.ψ := hpair.good
  have h2 : Module.finrank F E = 2 := hpair.base.cm.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let ev0 : Fn F n d →ₗ[ℂ] ℂ := LinearMap.proj (R := ℂ) (φ := fun _ : (Fin n × Fin d → AF F) => ℂ) 0
  have hmem : ∀ (w : Matrix (Fin n) (Fin d) (AE F E)) (Φ : Fn F n d), Φ ∈ schA F (Fin n × Fin d) →
      M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) :=
    fun w Φ hΦ => GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ _ Φ hΦ
  have hrec : ∀ S : Fn F n d →ₗ[ℂ] Fn F n d,
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho B.ψ z Φ) = M₁.co.rho B.ψ z (S Φ)) →
      ∀ Φ ∈ schA F (Fin n × Fin d), ∀ y, S Φ y = ev0 (S (M.co.rho B.ψ (M₁.co.e.symm (y, 0)) Φ)) := by
    intro S hS Φ hΦ y
    rw [hS _ Φ hΦ]
    simp [ev0, Darboux.rho, schr]
  obtain ⟨L, hiso, hrk, hL⟩ := exists_lagrangian (F := F) (R := AF F) (κ := Fin n × Fin d) (V := Matrix (Fin n) (Fin d) E)
    (by rw [Module.finrank_matrix, h2]; simp; ring) (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F)
    (M.co.e.toLinearMap.restrictScalars F ∘ₗ incL F E n d) (M₁.co.e.toLinearMap.restrictScalars F ∘ₗ incL F E n d)
    (fun x => by obtain ⟨y, z, h⟩ := hM.rat x; exact ⟨(y, z), h⟩)
    (fun x => by obtain ⟨y, z, h⟩ := hM₁.rat x; exact ⟨(y, z), h⟩)
    (M.co.e.injective.comp (incL_injective n d)) (M₁.co.e.injective.comp (incL_injective n d))
    (fun x y => (M.co.form _ _).symm.trans (M₁.co.form _ _))
  have inv : ∀ S : Fn F n d →ₗ[ℂ] Fn F n d,
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho B.ψ z Φ) = M₁.co.rho B.ψ z (S Φ)) →
      ∀ (t : AF F), ∀ w ∈ L, ∀ Φ ∈ schA F (Fin n × Fin d),
        (ev0 ∘ₗ S) (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) Φ) =
          (ev0 ∘ₗ S) Φ := by
    intro S hS t w hw Φ hΦ
    obtain ⟨x, hx, hx0⟩ := hL w hw
    have hx' : ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i))) = M.co.e (incM F x) := hx
    have hx1 : (M₁.co.e (incM F x)).1 = 0 := hx0
    have hz : (M₁.co.e (t • incM F x)).1 = 0 := by rw [map_smul, Prod.smul_fst, hx1, smul_zero]
    have he : schr B.ψ (t • M.co.e (incM F x)) Φ = M.co.rho B.ψ (t • incM F x) Φ := by
      rw [Darboux.rho, map_smul]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hx', he, hS _ Φ hΦ]
    generalize t • incM F x = z at hz
    simp [ev0, Darboux.rho, schr, hz]
  have hevh : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ z Φ) = M₁.co.rho B.ψ z (e Φ) := by
    intro z Φ hΦ
    have := hev.Heisenberg₂ z Φ hΦ
    have h1 : ∀ m : ℕ, incM F (1 : Matrix (Fin m) (Fin m) E) = 1 := fun m => by simp [incM]
    rwa [h1, h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at this
  obtain ⟨ei, ev, hei, hloc0, hloc⟩ := hev.loc
  have hex : ∀ v : Pl F, ∃ p : (Fin n × Fin d → Fv F v) → ℂ, p ∈ SB _ ∧
      ev v p = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      (M₁.vac v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
        p = M.vac v) := by
    intro v
    by_cases h : M₁.vac v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
    · exact ⟨M.vac v, (hM.vac v).1, by rw [← h]; exact (hloc0 v).1, fun _ => rfl⟩
    · have hmem' : Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∈
          (SB (Fin n × Fin d → Fv F v)).map (ev v) := by
        rw [(hloc0 v).2]; exact GlobalTheory.StdVacuum.indicator_mem_SB v
      obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.1 hmem'
      exact ⟨p, hp, hpe, fun h' => absurd h' h⟩
  choose φ hφSB hφev hφvac using hex
  have hcof : ∀ᶠ v in cofinite, φ v = M.vac v := by
    filter_upwards [hM₁.std] with v hv
    exact hφvac v hv
  have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hcof, hM.std] with v h1 h2
    rw [h1, h2]
  obtain ⟨g, hg⟩ : ∃ g, ei g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hei (ContinuousLinearMap.ext h)
  have hΦ₀ : pure g φ ∈ schA F (Fin n × Fin d) := (GlobalTheory.ThK.EvUniqInf.rest_pure g φ hφSB hstd).2
  have hne : e (pure g φ) ≠ 0 := by
    rw [hloc g φ hφSB hcof, show (fun v => ev v (φ v)) = fun v =>
      Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 from funext hφev]
    intro h0
    apply hg
    apply GlobalTheory.ThK.EvUniqInf.eq_of_pure_std (ei g) 0
    rw [h0]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  obtain ⟨y₀, hy₀⟩ := Function.ne_iff.1 hne
  obtain ⟨c, hc⟩ := GlobalTheory.SvNLinear.main hK.base F B.ψ hψ (Fin n × Fin d) L hiso hrk (ev0 ∘ₗ f) (ev0 ∘ₗ e) (inv f hfh) (inv e hevh)
    ⟨M.co.rho B.ψ (M₁.co.e.symm (y₀, 0)) (pure g φ), hmem _ _ hΦ₀, by
      rw [LinearMap.comp_apply, ← hrec e hevh _ hΦ₀ y₀]; exact hy₀⟩
  refine ⟨c, fun Φ hΦ => funext fun y => ?_⟩
  rw [hrec f hfh Φ hΦ y, Pi.smul_apply, hrec e hevh Φ hΦ y, smul_eq_mul]
  exact hc _ (hmem _ _ hΦ)

end GlobalTheory.ThK.EvChangeUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartitionSelectionEvaluation
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.RowsParts

variable {Bd : BdT} {𝒜 : FamClass} {σ : RawSel Bd 𝒜} {eps : ℝ} {Fm : FamP eps} {hc : 𝒜 Fm}

theorem ev_prem {p : Prop} {q : ℝ → BdP Bd} (h : p → ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C, C0 ≤ C → Ind.Ev σ Fm hc (q C)) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C, C0 ≤ C → Ind.Ev σ Fm hc fun D O c b => p → q C D O c b := by
  by_cases hp : p
  · obtain ⟨C0, h0, h⟩ := h hp
    refine ⟨C0, h0, fun C hC => ?_⟩
    obtain ⟨x0, h⟩ := h C hC
    exact ⟨x0, fun x hx hle i _ => h x hx hle i⟩
  · exact ⟨0, le_rfl, fun _ _ => ⟨0, fun _ _ _ _ h => absurd h hp⟩⟩

end GlobalTheory.Fc.RowsParts

namespace GlobalTheory.Fc

open RowsParts

theorem row_rRows_of_parts : ∀ (DR : R1.DefT) (Q : V4.Slot) (Lk : LkT Bundle), Row Q Lk (fun 𝒜 σ => ∃ τ : TieSel σ, Ind.EvWC (fun _ => True) Ind.Small 𝒜 (partSel σ τ) ∧ Ind.EvWC (fun _ => True) Ind.L3 𝒜 (partSel σ τ) ∧ Ind.EvWC (fun Fm => DIVinN Fm) Ind.ON 𝒜 (partSel σ τ) ∧ Ind.EvWC (fun _ => True) Ind.L6 𝒜 (partSel σ τ) ∧ Ind.EvWC (fun Fm => DIVinN Fm) Ind.FUN 𝒜 (partSel σ τ)) → Row Q Lk (Ind.EvW (Bd := Bundle) fun _ _ _ b => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) → Row Q Lk (Ind.EvW (Bd := Bundle) fun _ _ _ b => Formalism.L2.Rows.RowsHoldKap3 b.P) → Row Q Lk (Ind.EvWC (Bd := Bundle) (fun _ => True) fun C CH D O c b => DR D O c b C CH) → R1.RestRowsConditionAtBundlePoints DR Q Lk := by
  intro DR Q Lk h1 h2 h3 h4
  refine (h1.and (h2.and (h3.and h4))).imp fun 𝒜 σ _ H => ?_
  obtain ⟨⟨τ, hS, hL3, hON, hL6, hFUN⟩, hM, hK, hD⟩ := H
  have hw : ∀ {eps : ℝ} (Fm : FamP eps), GlobalTheory.Cp.D3 3 𝒜 Fm → W3 𝒜 Fm :=
    fun Fm h => (working_classes_frozen.1 𝒜 _ Fm).2.1 h
  have hall := Closed.and hS (Closed.and hL3 (Closed.and hON (Closed.and hL6 (Closed.and hFUN
    (Closed.and hM (Closed.and hK hD))))))
  refine Closed.imp (Pk.Closed.sub hall hw) fun Fm CH _ H hc => ?_
  obtain ⟨hS, hL3, hON, hL6, hFUN, hM, hK, hD⟩ := H
  have hc' := hw Fm hc
  obtain ⟨C1, p1, hS⟩ := hS hc' trivial
  obtain ⟨C2, -, hL3⟩ := hL3 hc' trivial
  obtain ⟨C3, -, hON⟩ := ev_prem (hON hc')
  obtain ⟨C4, -, hL6⟩ := hL6 hc' trivial
  obtain ⟨C5, -, hFUN⟩ := ev_prem (hFUN hc')
  obtain ⟨C6, -, hD⟩ := hD hc' trivial
  obtain ⟨C, k1, k2, k3, k4, k5, k6⟩ : ∃ C : ℝ, C1 ≤ C ∧ C2 ≤ C ∧ C3 ≤ C ∧ C4 ≤ C ∧ C5 ≤ C ∧ C6 ≤ C :=
    ⟨max C1 (max C2 (max C3 (max C4 (max C5 C6)))), by simp, by simp, by simp, by simp, by simp, by simp⟩
  obtain ⟨x1, hS⟩ := hS C k1
  obtain ⟨x2, hL3⟩ := hL3 C k2
  obtain ⟨x3, hON⟩ := hON C k3
  obtain ⟨x4, hL6⟩ := hL6 C k4
  obtain ⟨x5, hFUN⟩ := hFUN C k5
  obtain ⟨x6, hD⟩ := hD C k6
  obtain ⟨x7, hM⟩ := hM hc'
  obtain ⟨x8, hK⟩ := hK hc'
  obtain ⟨x0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :
      ∃ y : ℝ, x1 ≤ y ∧ x2 ≤ y ∧ x3 ≤ y ∧ x4 ≤ y ∧ x5 ≤ y ∧ x6 ≤ y ∧ x7 ≤ y ∧ x8 ≤ y :=
    ⟨max x1 (max x2 (max x3 (max x4 (max x5 (max x6 (max x7 x8)))))),
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  refine ⟨C, p1.trans k1, x0, fun x hx _ hle i => ⟨?_, hD x hx (l6.trans hle) i⟩⟩
  have s := hS x hx (l1.trans hle) i
  exact
    { w1 := s.1
      covol := hL3 x hx (l2.trans hle) i
      onto := hON x hx (l3.trans hle) i
      lamLow := fun _ => hL6 x hx (l4.trans hle) i
      seeIso := s.2.1
      miStar := hM x hx (l7.trans hle) i
      fun0 := hFUN x hx (l5.trans hle) i
      pass := s.2.2
      kap := hK x hx (l8.trans hle) i }

end GlobalTheory.Fc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowGoodLatticeNeBotStatement
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_good_lattice_ne_bot : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → RecTied D L → ∀ i : Fin D.R.m, latGood p.R.toRealDat p.F.lv2 i ≠ ⊥ := by
  first | exact @GlobalTheory.CovTop.latGood_ne_bot_at | exact GlobalTheory.CovTop.latGood_ne_bot_at | (intros; apply GlobalTheory.CovTop.latGood_ne_bot_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsOfAllPartPropertiesStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rows_of_all_part_properties : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : Ind.Part D O c), Ind.PFire D O c b → Ind.PRB D O c b → Ind.PPA D O c b → Ind.PFrames D O c b → Ind.PDiv D O c b → Ind.PNmj D O c b → Formalism.BasicNotions.GoodFTAll D → b.pt.Ties → Ind.PRows D O c b := by
  first | exact @GlobalTheory.Fc.Ind.pRows_of_parts | exact GlobalTheory.Fc.Ind.pRows_of_parts | (intros; apply GlobalTheory.Fc.Ind.pRows_of_parts <;> assumption)
end

