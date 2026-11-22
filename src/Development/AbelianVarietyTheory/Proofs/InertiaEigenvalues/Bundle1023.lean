import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0983
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1022
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1021
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexRationalTmulCoord
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSpanAndGoodRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0738
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0864
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0825
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0980
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1017
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0999
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0971
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0730
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0423
import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumsConjugateTwistsConjugateExpansions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceClassSum

theorem classSum_conj_place : ∀ (D : D7) (X : RealSide D) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), B.Good → ∀ ψ ψ' : Twist D Circle, ψ.Good → ψ'.Good → B.admitted ψ.Q →
  GlobalTheory.BigOn.Exp.TwConj.HasTuples X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j B ψ ψ' →
  ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) (cc : VsV D j ℂ →ₗ[ℂ] (X.R.cV j).W) (κ : ℂ), IsLow X j u → ExtC X.R.toRealDat j (inC (X.geo.O j).c') (X.geo.O j).c0' cc → κ ≠ 0 →
  ∀ τ : ℂ ≃+* ℂ, FixBase X.core X.R.toRealDat j τ → FixDat B τ → ConjChar τ ψ ψ' → ∀ ω ω' : PairRep (Vc D j) (Wc D j), B.IsWeil ψ.chi ω → B.IsWeil ψ'.chi ω' →
  ∃ ζ : ℂ, IsRoot1 ζ ∧ ∀ (I : Type) [Fintype I] (rep : I → GA D (Vc D j)), (∀ a, rep a ∈ GfC (Vc D j)) → ∀ F F' : Amb D j,
    ConjAt (X.R.ioP j (PiTensorProduct.tprod ℂ u) ∘ₗ cc) κ τ F F' →
    ConjFun (X.geo.O j) (X.geo.κ j) τ ζ (κ • B.classSum ω ψ rep F) (κ • B.classSum ω' ψ' rep F') := by
  intro D X j B hB ψ ψ' hψ hψ' hadm hT u cc κ hu hc hκ τ hτ hfd hcc ω ω' hω hω'
  obtain ⟨T0', A', R', F', v₀', O', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, t, t', ht, ht'⟩ := hT
  obtain ⟨c', u', hc', hu', hio⟩ := h11 cc u hc hu
  obtain ⟨ζ, hζ, H⟩ := GlobalTheory.T.conjugate_thetaSeries_flatVectors_twistedWeil GlobalTheory.chartIndependence_unconditional D _ _ T0' A' X.core R' F' X.geo.κ v₀' O' (fun _ => 1) X.size
    h1 h2 h3 h4 h5 j h6 h7 c' hc' u' hu' B hB h8 τ (h9 τ hτ) hfd ω ω' ψ ψ' t t' hω hω' hψ hψ' hadm ht ht' hcc
  have hz : GlobalTheory.ConjSpan.RelConj (O' j) (X.geo.κ j) τ :=
    GlobalTheory.ConjRelation.expands_zero_conj D _ _ T0' A' X.core R' F' X.geo.κ v₀' h1 h3 j Unit _ (O' j) h6.2 τ hτ.core
  refine ⟨ζ, hζ, fun I _ rep hrep F F' hF => h10 _ _ _ _ ?_⟩
  have := GlobalTheory.ConjSpan.classSum_conj (R'.ioP j (PiTensorProduct.tprod ℂ u')) c' hz hκ hcc.1 H I rep hrep F F' fun h => by
    obtain ⟨x, x', hx, e, e'⟩ := hF h
    exact ⟨x, x', hx, e.trans (hio x).symm, e'.trans (hio _).symm⟩
  rwa [one_mul] at this

end GlobalTheory.PlaceClassSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullRankThetaSeriesFormsOfRationalScalars
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.MainNotions.IntegralHeckeForms
open Formalism.IndefR.Links
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TieRank
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lin
variable {O O' V : Type} [CommRing O] [IsDomain O] [CommRing O'] [Algebra O O'] [AddCommGroup V]
  [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]

variable (O') in

def scR (a : FractionRing O) : O' ⊗[O] V →ₗ[O'] O' ⊗[O] V :=
  ((a • LinearMap.id : Module.End (FractionRing O) V).restrictScalars O).baseChange O'

end Lin

section Onto
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

end Onto

section Comparison₂
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

open GlobalTheory.SeriesTie

end Comparison₂

section Tie2
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

open GlobalTheory.SeriesTie

end Tie2

section Main
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

open GlobalTheory.SeriesTie

end Main

section Target
open GlobalTheory.TwInputs GlobalTheory.SeriesTie Formalism.MainNotions

theorem faithful_serSide {D : D7} (X : RealSide D) {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m)
    (b : Bool) : Faithful (Y.Z.rd i j b) :=
  realRd_faithful D X.Γ X.Pl0 X.I0 X.T X.A3 _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b (Y.Z.ν i j b)
    (Y.Z.scalar i j b).ne X.unif X.char.models.HW (Y.Z.vec j) ((GlobalTheory.T.rational_datum_small_field_form_hecke_scalar_unit D X E Y).1 _ (Nat.le_add_left _ _) j.2)

theorem rank_of_ties : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), ∀ i,
    BaseTup Y i → (∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b,
    FullRk D.nexp E i j b (SgJ D.nexp E i j b) := by
  intro hP D X E Y i hB hR
  have hG : ∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t :=
    GlobalTheory.AdSpan.goodRangeAt X.R.toRealDat hP X.size X.char.lev X.char.grp.record X.char.fam X.char.models X.char.thP
  exact GlobalTheory.T.averaged_series_full_rank_of_complex_span_good D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.tie (faithful_serSide X Y) E i (fun j b => (Y.Z.rat (hR j b)).1)
    (fun j hj b a => Y.all i j hj b a) (GlobalTheory.T.goodForms_spanned_by_thetaSeries_of_classSums D Y.Z.ρ Y.Z.good Y.Z.rd i (GlobalTheory.T.goodForms_classSums_of_projectedLift_range D X E Y hG i hB))

end Target

end GlobalTheory.TieRank

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalRowSeries
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.PlaceRead.SeriesAtState

theorem low_of_tiedC {D : D7} {Fr : TwFrameC D} (h : TwistFrameLowIndexCompatibility D Fr (lowAll D)) (i) (P : PlE D.host)
    (hP : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK * (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') : ℕ) :
      𝓞 D.host.E) ∈ P.asIdeal) : P ∈ D.ntw.S0 i := by
  have hp := P.isPrime
  have mem : ∀ p ∈ lowAll D, ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → P ∈ D.ntw.S0 i := fun p a b => by
    rw [← Finset.mem_coe, h.ringSpec_excludedPlaces_eq i]
    exact Or.inr (h.concreteTwistFrame_extraExcluded_over_smallPrimes i p a b)
  have key : ∀ m : ℕ, m ≠ 0 → ((m : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    intro m
    induction m using Nat.recOnMul with
    | zero => exact fun h0 => absurd rfl h0
    | one => exact fun _ h1 => absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h1)) hp.ne_top
    | prime p pp => exact fun _ h1 => ⟨p, pp, dvd_rfl, h1⟩
    | mul a b iha ihb =>
      intro h0 h1
      rw [Nat.cast_mul] at h1
      rcases hp.mem_or_mem h1 with h1 | h1
      · obtain ⟨p, p1, p2, p3⟩ := iha (left_ne_zero_of_mul h0) h1
        exact ⟨p, p1, p2.mul_right _, p3⟩
      · obtain ⟨p, p1, p2, p3⟩ := ihb (right_ne_zero_of_mul h0) h1
        exact ⟨p, p1, p2.mul_left _, p3⟩
  simp only [Nat.cast_mul] at hP
  rcases hp.mem_or_mem hP with hP | hP
  · rcases hp.mem_or_mem hP with hP | hP
    · rcases hp.mem_or_mem hP with hP | hP
      · obtain ⟨p, p1, p2, p3⟩ := key _ D.host.QS_pos.ne' hP
        refine mem p (Finset.mem_union_left _ ?_) p3
        refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_))
        exact Nat.mem_primeFactors.2 ⟨p1, (D.host.dvd_natAbs_discr_iff p1).2 (p2.trans D.host.QS_dvd_condN),
          Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)⟩
      · refine mem _ (Finset.mem_union_left _ ?_) hP
        refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_))
        exact Nat.mem_primeFactors.2 ⟨D.host.hyp.1, GlobalTheory.TwInputs.JoinModel.q_dvd_discr D,
          Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)⟩
    · have hN : Ideal.absNorm D.host.ccK ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
      obtain ⟨p, p1, p2, p3⟩ := key _ hN hP
      refine mem p (Finset.mem_union_left _ ?_) p3
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Nat.mem_primeFactors.2 ⟨p1, p2, hN⟩)))
  · rcases hp.mem_or_mem hP with hP | hP
    · rcases hp.mem_or_mem hP with hP | hP
      · rcases hp.mem_or_mem hP with hP | hP
        · exact mem _ (by simp [lowAll]) hP
        · exact mem _ (by simp [lowAll]) hP
      · exact mem _ (by simp [lowAll]) hP
    · exact mem _ (by simp [lowAll]) hP

theorem ratRow_at_state : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ _ x => ∀ (l : StrictHenselianAcyclic hL x) (i : (Dof x).ntw.Tw), (Dof x).ntw.NonzeroIndexPlace i → ∀ j b, GlobalTheory.SeriesTie.RatRow l.b.YS x.m.z.geo.v₀ l.b.ser.ex.good i j b := by
  intro hP hS hLL
  have ev : ∀ {Q : Ctx → Prop}, Ev Q → StepW Start fun K _ _ _ _ => Q K := fun h =>
    Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)
  have hF : StepW Start fun _ B f T w => ∀ (Z : w.Lt) (X : GlobalTheory.TwInputs.RealSide (w.st Z).toD7), X.R.C = (TC.cf w.I w.l Z) →
      GlobalTheory.TwInputs.FieldOk X :=
    EvG.imp (GlobalTheory.TwInputs.SmallField.evLgG_fieldOk hP) fun _ _ _ _ _ H => H.imp fun _ _ _ _ G hK _ _ w _ Z => (G hK _ w Z).1
  refine (((((ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).and (ev GlobalTheory.Mem.StdSize.vstd_size_ev)).and hF).and (sXd_all hLL)).and
    (GlobalTheory.T.series_character_inverse hLL)).trans (StepW.of_all fun K B f T w hO _ H => ?_)
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := H
  intro P x l
  obtain ⟨hHo, -⟩ := h1 (w.st x.o.Z) hO
  obtain ⟨hStd, hSize⟩ := h2 (w.st x.o.Z) hO
  have hfin : Finite (TupU w.I (usedOf w.I T P.Wt)) := Finite.of_injective _ (ixOf_injective w.I _)
  let X := GlobalTheory.TwInputs.RealSide.ofPins x.m.z.geo x.m.z.pins x.m.intersectionNumber_baseChange x.m.inGeo hfin hHo hStd hSize
  have hX : GlobalTheory.TwInputs.FieldOk X := h3 x.o.Z X x.m.z.lev.C
  obtain ⟨xd, hxd⟩ := h4 P x ⟨l.toLI, l.b.toSeriesState⟩
  obtain ⟨hU, hψ⟩ := h5 P x l
  obtain ⟨f', s1, s2, s3⟩ := GlobalTheory.T.exists_rationalHeckeOperators_adelicReading hP.decay hS.hkTr hS.hkRead (Dof x) X _ l.b.YS
  obtain ⟨H, r1, r2⟩ := GlobalTheory.TwInputs.AtLayer.exists_hecke X _ l.b.YS l.b.ser.ex f' s1 s2 s3 l.b.Bs.cHk l.b.Bs.cHk_del
    (GlobalTheory.TwInputs.AtLayer.hkF_zero_of_sideB l.b.Bs l.rat.In.hL_zero)
  let Y : GlobalTheory.TwInputs.SerSide X (twEOf xd) :=
    { S := _
      YS := l.b.YS
      sup := l.b.ser.sup
      H := H
      reads := r1
      del := r2
      Z := l.b.ser.ex
      U_eq := hU
      psi_eq := hψ
      low := low_of_tiedC l.b.Bs.tw
      Sb := fun i Q hQ => by
        have hA : x.m.z.R.Sb = x.m.z.R.Pg := x.m.z.pins.char.allPl
        obtain ⟨k, hk⟩ := l.b.ser.ex.good.Pg i ⟨0, lt_of_lt_of_le two_pos B.R.two_le_m⟩ true Q
          (by rw [l.b.ser.ex.pin.Pg]; exact hA ▸ hQ)
        exact (Dof x).ntw.placesOver_subset_exceptional i k hk
      B_range := fun i _ j _ b => l.b.Bs.tw.B_range i j b
      hk_emb := fun i j b k P y h1 h2 h => l.b.Bs.hk_emb i j b k P y h1 h2 h.2.2.2 h.2.2.1 h.2.1
      hk_split := fun i _ j _ b k P h => by
        obtain ⟨s, hs⟩ := l.b.Bs.tw.hk_split i j b k P h.2.2.2
        exact hs ▸ Polynomial.Splits.multisetProd fun p hp => by
          obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hp
          exact Polynomial.Splits.X_sub_C a
      off := fun i _ => ⟨fun j hj b => l.b.ser.off i j b fun h => hj (Finset.mem_Icc.2 h), l.b.Bs.hEig_zero i⟩
      all := fun i j hj b a => by
        have := hxd i j b (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2
        change a ∈ xd.xd0 i j b
        rw [this]; trivial }
  exact (GlobalTheory.T.thetaSeries_rationality_and_coefficientBound hP.decay hP.what₂.art hS.rat hS.int (Dof x) X _ Y hX).1

end GlobalTheory.PlaceRead.SeriesAtState
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistOfCuspParamsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_of_cusp_params : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL (fun _ _ _ _ w Z _ _ _ _ _ c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw) → EvLgG fun K B f T => KPx B f → T = TwDat.untw B T.pl → ∀ w Z Wt p0 t nch n xd c, Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RX K B f T w Z Wt p0 t) → ColPin w → Nonempty (GlobalTheory.TwInputs.TwOf hL K B f T w Z Wt p0 t nch n xd c) := by
  first | exact @GlobalTheory.TwInputs.AtLayer.twOf_of_layer | exact GlobalTheory.TwInputs.AtLayer.twOf_of_layer | (intros; apply GlobalTheory.TwInputs.AtLayer.twOf_of_layer <;> assumption)
end

