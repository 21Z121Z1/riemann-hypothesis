import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0005
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.Bundle0018
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0020
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0033
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0042
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0022
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVPatch
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Af.Bc GlobalTheory.RealGal UpperTheory.V.Af.ExLib
open private UpperTheory.V.Z.Win.SplitTorusFixedPoints.plainTor_of_iso from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.SplitTr
namespace UpperTheory.Gal.SV
theorem attRes_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (P : CuspSub K a), IsBC π P → ∀ (r : G K Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (K →+* Qbar l) → Multiset ℤ), UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) P ι r wt HT → AttRes π ι K r := by
  intro L F Ω _ _ _ _ _ _ K _ _ _ _ _ _ _ l _ ι a ha π P hBC r wt HT H
  have hloc := _root_.GlobalTheory.T.local_global_compatibility_complex_alt L
  have hsl := GlobalTheory.T.satakeParameters_local
  refine (hBC.unr.and (eventually_not_mem K l)).mono ?_
  rintro w ⟨hu, hw⟩ f hf
  obtain ⟨B, hB, hBw⟩ := hu (w.under (𝓞 F)) rfl f hf
  refine ⟨B, hB, ?_⟩
  obtain ⟨⟨σ, hσ⟩, hi⟩ := hloc K a P w
  have hS := ((hsl K a w σ).2 _ P.finPart (hi σ hσ) _).1 hBw
  have h1 := frob_of (ι := ι) (r := r) hw σ hS fun A h rc hrc => by
    have g := gdOf K Ω A w h rc hrc a σ ((plainOf K a ha P w).2 ⟨_, hBw⟩ σ hσ)
    rw [← (H.away w hw A h rc hrc σ hσ).tor g.1 g.2]
    exact isWDOf_wdOf (h := h) hw ι (Units.continuous_val.comp H.cont)
  rwa [hf, GlobalTheory.RealGal.AttResProof.algSat_pow] at h1
section Descent
variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ}
theorem local_condition_at_place_of_decomposition_le_range (L : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (ha : 1 ≤ a) {K : Type} [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure K Ω] {ι : Qbar l ≃+* ℂ} {π : TR.CuspSub F a} {P : CuspSub K a} (hBC : IsBC π P)
    {r : G F Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (K →+* Qbar l) → Multiset ℤ}
    (hG : UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) P ι (r.comp (res F Ω K)) wt HT) {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A v) (hdec : Dec (F := F) A ≤ (res F Ω K).range) {HTF : (F →+* Qbar l) → Multiset ℤ}
    (hHT : ∀ τ : K →+* Qbar l, HT τ = HTF (τ.comp (algebraMap F K))) : At π ι r HTF h := by
  obtain ⟨w, h', i, hi⟩ := GlobalTheory.T.exists_place_completion_iso F Ω K v A h hdec
  have hlw : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ((l : ℕ) : 𝓞 K) ∉ w.asIdeal := fun hl hw => by
    apply hl
    have e1 := (h ((l : ℕ) : 𝓞 F))
    have e2 := (h' ((l : ℕ) : 𝓞 K))
    simp only [map_natCast] at e1 e2
    exact e1.1 (e2.2 hw)
  have ST := splitTr F K a ha π P hBC v w i ⟨hi.cont, hi.loc⟩
  obtain ⟨⟨σ', hσ'⟩, -⟩ := _root_.GlobalTheory.T.local_global_compatibility_complex_alt L K a P w
  obtain ⟨rc', hrc'⟩ := recTExists K Ω A w h'
  obtain ⟨S, hS, -⟩ := GlobalTheory.T.place_over_transport_ring_iso_symm F Ω A v h K Ω A w h' _ _ i hi
  have inj : ∀ {x y : WD h} {x' y' : WD h'}, WDRel (RingEquiv.refl Ω) x x' → WDRel (RingEquiv.refl Ω) y y' → x' = y' → x = y :=
    fun hx hy e => S.injective (by rw [(hS _ _).1 hx, (hS _ _).1 hy, e])
  have up : ∀ σ, π.IsLocComp v σ → GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) → Gd (rc' (algNorm σ')) := fun σ hσ hp => by
    obtain ⟨e, he⟩ := hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'
    exact gdOf K Ω A w h' rc' hrc' a σ' (UpperTheory.V.Z.Win.SplitTorusFixedPoints.plainTor_of_iso i hi.cont
      (GlobalTheory.LocalFieldIso.continuous_symm i hi.cont) _ _ _ _ e he hp)
  have br : ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), Induces Bw →
      ∃ (Bw' : LocBridge l K Ω (Dec (F := K) A) O) (_ : Induces Bw'), Bw'.Kw = Bw.Kw ∧ Bw'.j = Bw.j ∧ Bw'.LL = Bw.LL :=
    fun O _ _ _ Bw hj => by
      obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge F K Ω l A O Bw (GlobalTheory.T.local_field_embedding_mem F Ω K l A O Bw hdec)
      exact ⟨Bw', fun x => by rw [e2]; exact hj x, e1, e2, e3⟩
  refine ⟨fun B hB => ST.1.2 ((plainOf K a ha P w).2 (ST.2 ⟨B, hB⟩)), fun σ hσ hp rc hrc => ?_, fun σ hσ hp O _ _ _ Bw hj => ?_,
    fun hl hp => ?_, fun O _ _ _ Bw hj σ hσ hs => ?_⟩
  · obtain ⟨e, he⟩ := hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'
    have hy := recTr L.aut.art hi σ σ' e he hrc hrc' hp
    have g := up σ hσ hp
    refine ⟨fun hl => ?_, fun O _ _ _ Bw hj _ => ?_⟩
    · obtain ⟨x, hx, hxx⟩ := GlobalTheory.T.galois_rep_restriction_local_completion F Ω K l ι a r A v w h h' i hi _
        (isWDOf_wdOf (h := h') (hlw hl) ι (Units.continuous_val.comp hG.cont))
      exact ⟨x, hx, fun _ => inj hxx hy ((hG.away w (hlw hl) A h' rc' hrc' σ' hσ').tor g.1 g.2)⟩
    · obtain ⟨Bw', hj', e1, e2, e3⟩ := br O Bw hj
      obtain ⟨-, a2, -, a4⟩ := (hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').nice σ' hσ' rc' hrc' (Or.inr g.1) g.2
      have hpst := (GlobalTheory.T.local_embedding_compatible_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r).2.2.2.1 a2
      exact ⟨hpst, inj (GlobalTheory.T.local_embedding_restrict_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r hpst ι v w h h' hj hj' i hi) hy (a4.tor g.1 g.2)⟩
  · have g := up σ hσ hp
    obtain ⟨Bw', hj', e1, e2, e3⟩ := br O Bw hj
    obtain ⟨a1, -, a3, -⟩ := (hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').nice σ' hσ' rc' hrc' (Or.inr g.1) g.2
    have D := GlobalTheory.T.local_embedding_compatible_extension F Ω K l (Loc.PP l) A O Bw Bw' e1 e2 e3 a r
    refine ⟨D.1 a1, fun τ LL' τ' hτ => ?_⟩
    obtain ⟨τK, τ'', hτK, hind⟩ := GlobalTheory.T.local_embedding_agree F Ω K l A O Bw Bw' e1 e2 τ LL' τ' hτ
    have hJ := D.2.2.2.2 τK (HT τK) (a3 τK LL' τ'' hind)
    rw [hHT τK, hτK] at hJ
    exact hJ
  · have hp' := ST.1.1 hp
    have g := gdOf K Ω A w h' rc' hrc' a σ' (hp' σ' hσ')
    obtain ⟨t, ht⟩ := winPt UpperTheory.V.Z.Gam.suppFacts UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winOf K a ha P
    obtain ⟨x, hx, hxx⟩ := GlobalTheory.T.galois_rep_restriction_local_completion F Ω K l ι a r A v w h h' i hi _
      (isWDOf_wdOf (h := h') (hlw hl) ι (Units.continuous_val.comp hG.cont))
    rw [hx.wdOf_eq hl]
    refine UpperTheory.GalN.V.RatioW.descend hi hxx ?_
    rw [(hG.away w (hlw hl) A h' rc' hrc' σ' hσ').tor g.1 g.2]
    exact ratioT K Ω A w h' rc' hrc' a P t (ht w hp') σ' hσ'
  · obtain ⟨e, he⟩ := hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'
    obtain ⟨Bw', hj', e1, e2, e3⟩ := br O Bw hj
    exact (GlobalTheory.T.local_embedding_compatible_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r).2.2.1
      ((hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').crys σ' hσ' ((GlobalTheory.T.aux_statement_23 F K v w i hi.cont a σ σ' e he).2 hs)).1
end Descent
theorem galois_rep_exists_totally_real_rank_two_of_base_change : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → UpperTheory.V.Z.Bc.QuadBC2 → AdmissibleReal → GaloisRepExistsTotallyRealGL2 := by
  intro litN qbc adm F Ω _ _ _ _ _ _ l _ ι a ha2 ha π χ hreg hpol
  let S : Set (QCM F Ω) := {Q | ∃ P : CuspSub ↥Q.K a, IsBC π P}
  have good : ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v →
      {Q : QCM F Ω | Dec (F := F) A ≤ (res F Ω ↥Q.K).range ∧ ∃ P : CuspSub ↥Q.K a, IsBC π P}.Infinite := by
    intro v A hA
    obtain rfl := ha2.out
    have hT := GlobalTheory.T.eventually_has_satake_parameters adm F 2 π
    refine (GlobalTheory.T.infinite_quadratic_fields_split_inertia F Ω (fun u => ∃ B, π.HasSat u B) hT v A hA).mono ?_
    rintro Q ⟨hdec, u, A', ⟨B, hB⟩, hA', hine⟩
    refine ⟨hdec, ?_⟩
    rcases qbc F Q.K Q.two π hreg with ⟨η, hq, htw⟩ | hP
    · exact absurd (_root_.GlobalTheory.T.inertia_le_range_of_unramified_alt litN F Ω Q.K Q.two η hq u A' hA' (unrAt_of_isoTwist adm F 2 ha π η htw u B hB)) hine
    · exact hP
  obtain ⟨v0⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩⟩
  obtain ⟨A0, hA0⟩ := ReciprocityTheory.Gal.exists_isPlaceOver (F := F) Ω v0
  have hS : S.Infinite := (good v0 A0 hA0).mono fun Q hQ => hQ.2
  have key : ∀ Q : ↥S, ∃ (P : CuspSub ↥Q.1.K a)
      (r : G ↥Q.1.K Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (↥Q.1.K →+* Qbar l) → Multiset ℤ),
      IsBC π P ∧ UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) P ι r wt HT := by
    rintro ⟨Q, P, hP⟩
    obtain ⟨hregP, χ', hχ'⟩ := _root_.GlobalTheory.T.regular_algebraic_and_polarized_of_quadratic_base_change litN F ↥Q.K Q.two a ha π χ P hreg hpol hP
    obtain ⟨r, wt, HT, hr⟩ := _root_.UpperTheory.Gal.SV.rowOf' litN.aut.gal ↥Q.K Ω l ι a ha P χ' hregP hχ'
    exact ⟨P, r, wt, HT, hP, hr⟩
  choose P r wt HT hP hr using key
  have hatt : ∀ Q, Continuous (r Q) ∧ IsSSRep (r Q) ∧ AttRes π ι ↥Q.1.K (r Q) := fun Q =>
    ⟨(hr Q).cont, (hr Q).ss,
      _root_.UpperTheory.Gal.SV.attRes_alt litN F Ω ↥Q.1.K l ι a ha π (P Q) (hP Q) (r Q) (wt Q) (HT Q) (hr Q)⟩
  obtain ⟨ρ, hρc, hρs, hev⟩ := GlobalTheory.T.galois_rep_patching_infinite_family F Ω l ι a π S hS r hatt
  obtain ⟨HTF, hcard, hwts, hbc⟩ := hodgeTate F Ω l ι a π hreg
  have hgal : ∀ᶠ Q : ↥S in Filter.cofinite,
      UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) (P Q) ι (ρ.comp (res F Ω ↥Q.1.K)) (wt Q) (HT Q) :=
    hev.mono fun Q hQ => props_iso (hr Q) hQ.1 hQ.2
  have hHT : ∀ Q : ↥S, (∀ τ : ↥Q.1.K →+* Qbar l, HT Q τ = HTF (τ.comp (algebraMap F ↥Q.1.K))) ∧
      ∀ τ : F →+* Qbar l, HTF τ = (HTF τ).map (wt Q - ·) :=
    fun Q => hbc ↥Q.1.K Q.1.two (P Q) (hP Q) (r Q) (wt Q) (HT Q) (hr Q)
  obtain ⟨Q0⟩ : Nonempty ↥S := hS.nonempty.to_subtype
  let τ0 : F →+* Qbar l := ι.symm.toRingHom.comp (Classical.arbitrary (InfinitePlace F)).embedding
  have hwt : ∀ Q : ↥S, wt Q = wt Q0 := fun Q =>
    GlobalTheory.T.eq_of_multiset_symmetric_reflections (HTF τ0) (wt Q) (wt Q0) (by rw [← Multiset.card_pos, hcard]; exact ha) ((hHT Q).2 τ0) ((hHT Q0).2 τ0)
  have hpick : ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v →
      ∃ Q : ↥S, Dec (F := F) A ≤ (res F Ω ↥Q.1.K).range ∧
        UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) (P Q) ι (ρ.comp (res F Ω ↥Q.1.K)) (wt Q) (HT Q) := by
    intro v A hA
    have hfin := (Filter.eventually_cofinite.1 hgal).image Subtype.val
    obtain ⟨Q, hQ, hQn⟩ := ((good v A hA).diff hfin).nonempty
    refine ⟨⟨Q, hQ.2⟩, hQ.1, ?_⟩
    by_contra hc
    exact hQn ⟨⟨Q, hQ.2⟩, hc, rfl⟩
  have hD : ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A v), At π ι ρ HTF h := fun v A h => by
    obtain ⟨Q, hdec, hQ⟩ := hpick v A h
    exact _root_.UpperTheory.Gal.SV.local_condition_at_place_of_decomposition_le_range litN ha (hP Q) hQ h hdec (hHT Q).1
  have hpl : ∀ w B, π.HasSat w B → PlainAtR π w := fun w B hB => by
    obtain ⟨A, h⟩ := ReciprocityTheory.Gal.exists_isPlaceOver (F := F) Ω w
    exact (hD w A h).plain B hB
  refine ⟨ρ, wt Q0, HTF, hρc, hρs, hpl, fun w σ hσ hp => ⟨fun A h => (hD w A h).cmp σ hσ hp, fun A h => (hD w A h).ht σ hσ hp⟩,
    fun w hw B hB => ?_, fun w hw A h => (hD w A h).ratio hw, hwts, (hHT Q0).2, fun w A h => (hD w A h).crys⟩
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := GlobalTheory.T.local_global_compatibility_real adm F a π w
  have hS := ((GlobalTheory.T.satakeParameters_local F a w σ).2 _ π.finPart (hiso σ hσ) B).1 hB
  exact frob_of hw σ hS fun A h rc hrc => (((hD w A h).cmp σ hσ (hpl w B hB σ hσ) rc hrc).1 hw).isWDOf
    (gdOf F Ω A w h rc hrc a σ (hpl w B hB σ hσ))
end UpperTheory.Gal.SV
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVRPropMV
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
namespace UpperTheory.Esk.PropMVAux
variable {l : ℕ} [Fact l.Prime]
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
end UpperTheory.Esk.PropMVAux
open UpperTheory.Esk.PropMVAux in
open Classical in
theorem UpperTheory.Esk.pf_PropMV_sv_alt : _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.PropMHol → UpperTheory.Esk.HolWC → UpperTheory.Esk.HRep → UpperTheory.Esk.PropMV := by
  intro hPH hMH hWC hHR F Ω _ _ _ _ _ _ l _ hl2 hd hsplit ι ξ ho hodd hunr hram P hP1 hP2
  have : IsGalois F Ω := {}
  obtain ⟨art, ha⟩ := hPH.litN.aut.art F Ω
  have hc := continuous_of_isOpen_ker' ξ ho
  have : Finite (G F Ω ⧸ ξ.ker) := ξ.ker.quotient_finite_of_isOpen ho
  have hm : 0 < ξ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hξm : ξ ^ ξ.ker.index = 1 := MonoidHom.ext fun g => by
    rw [MonoidHom.pow_apply, ← map_pow]
    exact ξ.ker.pow_index_mem g
  have hn : ∀ s, ‖(ξ s : Qbar l)‖ = 1 := fun s => by
    have h2 : ξ s ^ ξ.ker.index = 1 := DFunLike.congr_fun hξm s
    have h3 : ‖(ξ s : Qbar l)‖ ^ ξ.ker.index = 1 := by rw [← norm_pow, ← Units.val_pow_eq_pow_val, h2]; simp
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h3
  obtain ⟨ω, ⟨hω, hL⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι ξ hc hm hξm
  have hfo : IsOfFinOrder ω := isOfFinOrder_iff_pow_eq_one.2 ⟨_, hm, hω⟩
  obtain ⟨c, hcond, hc0, hfin⟩ := cond_ex ω hm hω
  have hine : ∀ (w : Pl F) (A : ValuationSubring Ω), IsPlaceOver A w → (Ine (F := F) A ≤ ξ.ker ↔ c w = 0) := fun w A hA =>
    (hL.unr_iff ha (Or.inr rfl) hA).trans (hc0 w).symm
  have hcl : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → c w = 0 := fun w hw => by
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    exact (hine w A hA).1 (hunr A (by simpa using (hA _).2 hw))
  have hfr : ∀ (w : Pl F), c w = 0 → ∀ A, IsPlaceOver A w → ∀ σ : G F Ω, IsFrob A (normV w) σ →
      ι.symm (ω.val w : ℂˣ) = (ξ σ⁻¹ : (Qbar l)ˣ) := fun w hw A hA σ hσ => by
    rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) ((hc0 w).1 hw) hA hσ, inv_inv]
  have hsg : ∀ v, ω.locInf v (-1) = -1 := fun v => by
    obtain ⟨j, σ, hσ, rfl⟩ := GlobalTheory.HilbertFromArtin.exists_conj (Ω := Ω) v (IsTotallyReal.isReal v)
    have e := hL _ σ (GlobalTheory.HilbertFromArtin.art_sign_eq ha j σ hσ)
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one, hodd σ ⟨j, hσ⟩] at e
    refine Units.ext (ι.symm.injective (e.symm.trans ?_))
    simp
  have hex : ∃ w, c w ≠ 0 := by
    obtain ⟨u, A, -, hA, hnA⟩ := hram
    exact ⟨u, fun h => hnA ((hine u A hA).2 h)⟩
  have hnc : ∀ w : Pl F, (((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ∃ A, IsPlaceOver A w ∧ ∃ σ ∈ Dec (F := F) A, ¬ Cong (ξ σ) 1) →
      ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ¬ ‖ι.symm (ω.val w : ℂˣ) - 1‖ < 1 := by
    rintro w ⟨hw, A, hA, σ, hσ, h⟩
    exact ⟨hw, fun h' => h (dec_cong ha hc hL ((hc0 w).1 (hcl w hw)) h' hA hσ)⟩
  obtain ⟨k, hkB, hk, φ, lam, hφ, hcu, hlam⟩ := hMH F l hl2 ι ω c hfo hsg hcond hex hcl P
    (hP1.imp fun w h => ⟨h.1, hnc w h.2⟩) (hP2.imp fun w h => ⟨h.1, hnc w h.2⟩) 3
  have hlev : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → levL l c w = c w := fun w hw => if_neg hw
  have hlev1 : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → levL l c w = 1 := fun w hw => if_pos hw
  have hfinL : {w | levL l c w ≠ 0}.Finite := by
    refine (hfin.union (fin_l (l := l))).subset fun w hw => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    exact hw ((hlev w h.2).trans h.1)
  have heu : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ‖ι.symm (eisT l ω c P w)‖ = 1 := fun w hw => by
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨σ, hσ⟩ := exists_isFrob hA
    rw [eisT, if_pos hw]
    split_ifs
    · rw [hfr w (hcl w hw) A hA σ hσ, hn]
    · simp
  obtain ⟨D⟩ := Wc.exL F l ι hsplit
  have hu2 : ∃ u, levL l c u ≠ 0 ∧ normV u = 2 := by
    obtain ⟨u, A, h2, hA, hnA⟩ := hram
    refine ⟨u, ?_, h2⟩
    by_cases hl : ((l : ℕ) : 𝓞 F) ∈ u.asIdeal
    · rw [hlev1 u hl]; exact one_ne_zero
    · rw [hlev u hl]; exact fun h => hnA ((hine u A hA).2 h)
  have hunit : ∀ v, Wc.nu ι (lam (D.pl v)) = 1 := fun v => by
    rw [nu_eq]
    refine norm_eq_one (heu _ (D.mem v)) ?_
    rw [← map_sub]
    exact hlam _
  obtain ⟨t, htB, ht, φ', lam', hV, hne, hcusp, heig, hcong⟩ :=
    hWC F hd l hl2 ι D (k + 1) (by omega) (levL l c) hfinL (fun v => hlev1 _ (D.mem v)) hu2 ω hfo φ lam hφ hcu hunit
      {v | D.pl v ∈ P} 2
  have hlam' : ∀ w, ‖ι.symm ((∏ v, if D.pl v = w ∧ v ∈ {v | D.pl v ∈ P} then (l : ℂ) ^ t else 1) * lam' w -
      eisT l ω c P w)‖ < 1 := fun w => by
    rw [← sub_add_sub_cancel _ (lam w), map_add]
    exact add_lt (nu_lt.1 (hcong w)) (hlam w)
  have haway : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ‖ι.symm (lam' w - eisT l ω c P w)‖ < 1 := fun w hw => by
    have h := hlam' w
    rwa [prod_away D _ t w hw, one_mul] at h
  obtain ⟨π, hreg, ⟨χ, hpol⟩, hinf, hU, hsat⟩ := hHR F (k + 1) (by omega) (fun v => if v ∈ {v | D.pl v ∈ P} then t else 0)
    (levL l c) ω hfo φ' lam' hV hne heig hcusp
  obtain ⟨r, wt, HT, hG, hatt, -⟩ := _root_.UpperTheory.Gal.SV.exRS_alt hPH.toClassicalTheorems F Ω l ι 2 one_le_two π χ hreg hpol
  obtain ⟨hdet, hres⟩ := det_res ξ hc r hG.cont k hk hn
    (((Filter.eventually_cofinite.1 hatt.2).union hfin).union (fin_l (l := l))) fun w hw A hA σ hσ => by
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hw
      obtain ⟨⟨⟨B₁, hB₁, hF⟩, h0⟩, hl⟩ := hw
      obtain ⟨B₂, hB₂, e⟩ := hsat w ((hlev w hl).trans h0)
      obtain rfl := hB₁.unique hB₂
      obtain ⟨h2, h3⟩ := tr_det ι _ _ _ (((hF A hA).2 σ hσ).trans e)
      have h4 := haway w hl
      rw [eisT, if_neg hl, if_pos h0, map_sub, map_add, map_one, hfr w h0 A hA σ hσ] at h4
      rw [h2, h3, map_mul, hfr w h0 A hA σ hσ, map_pow, map_natCast, cyc_frob hl hA hσ]
      exact ⟨h4, rfl⟩
  refine ⟨k, t, by omega, htB, hk, ht, levL l c, fun w => ι.symm (eisT l ω c P w), π, r,
    ⟨hreg, ⟨χ, hpol⟩, hG.cont, hatt, hdet, ho, hfinL, fun w A hA => ?_, fun w hw => ?_, fun w hw hl => ?_, fun w hw => ?_⟩,
    hres, fun w hw A hA σ hσ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hine w A hA]
    by_cases hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
    · simp [hl, hcl w hl]
    · simp [hl, hlev w hl]
  · obtain ⟨v, h1, h2, -⟩ := hU w
    rw [hw] at h2
    exact ⟨v, h1, h2⟩
  · refine ⟨lam' w, hU w, norm_one_of ?_⟩
    have h4 := haway w hl
    rwa [eisT, if_neg hl, if_neg (hlev w hl ▸ hw), map_sub, map_one] at h4
  · obtain ⟨v₀, hv₀⟩ := D.surj w hw
    have hnorm : normV w = l := hv₀ ▸ D.norm v₀
    have hc' := hlam' w
    rw [prod_at D _ t w v₀ hv₀] at hc'
    refine ⟨hlev1 w hw, ?_, ?_, heu w hw, ⟨lam' w, hlev1 w hw ▸ hU w, ?_⟩, fun τ hτ => ?_⟩
    · by_cases h : w ∈ P <;> simp [h] <;> omega
    · by_cases h : w ∈ P <;> simp [h] <;> ring
    · rw [hnorm]
      by_cases h : w ∈ P
      · have hv : v₀ ∈ {v | D.pl v ∈ P} := by simpa [hv₀] using h
        rw [if_pos hv, map_sub, map_mul, map_pow, map_natCast, mul_comm] at hc'
        rw [if_pos h]
        simpa using hc'
      · have hv : v₀ ∉ {v | D.pl v ∈ P} := by simpa [hv₀] using h
        rw [if_neg hv, one_mul, map_sub] at hc'
        rw [if_neg h]
        simpa using hc'
    · obtain ⟨v, hvd⟩ : ∃ v, InfinitePlace.mk (ι.toRingHom.comp τ) = v := ⟨_, rfl⟩
      have hv : D.pl v = w := hvd ▸ (D.embAt τ w).1 hτ
      rw [hvd]
      convert hinf v using 3
      by_cases h : w ∈ P
      · have hS : v ∈ {v | D.pl v ∈ P} := by simpa [hv] using h
        ext i; fin_cases i <;> simp [h, hS] <;> omega
      · have hS : v ∉ {v | D.pl v ∈ P} := by simpa [hv] using h
        ext i; fin_cases i <;> simp [h, hS] <;> omega
  · simp only [eisT, if_pos hw, if_pos h]
    exact hfr w (hcl w hw) A hA σ hσ
  · simp only [eisT, if_pos hw, if_neg h, map_one]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAboveW
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc Lp)
open scoped Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.GalN.V UpperTheory.V.Z.Win UpperTheory.Zero.LLC
open UpperTheory.V.Z.Sym.AboveWeight
section
section
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
  {w : Plc L} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion L)ˣ}
private theorem noLk_of {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (u : kˣ →* ℂˣ) (H : ∀ i j : Fin 3, i ≠ j → (![u, 1, u⁻¹] : Fin 3 → kˣ →* ℂˣ) i ≠ (![u, 1, u⁻¹] : Fin 3 → kˣ →* ℂˣ) j ∧
      (![u, 1, u⁻¹] : Fin 3 → kˣ →* ℂˣ) i ≠ (![u, 1, u⁻¹] : Fin 3 → kˣ →* ℂˣ) j * absPow k 1) :
    UpperTheory.V.Z.Sym.W.NoLk u := by
  intro j hj e he hE
  have e1 : absPow k (((1 : ℤ) : ℂ)) = absPow k 1 := by simp
  have e2 : absPow k (((-1 : ℤ) : ℂ)) = (absPow k 1)⁻¹ := by
    rw [show (((-1 : ℤ) : ℂ)) = -1 by simp, absPow_neg]
  rcases hj with rfl | rfl <;> rcases he with rfl | rfl
  · rw [pow_one, e1] at hE
    exact (H 0 1 (by decide)).2 (by simpa using hE)
  · rw [pow_one, e2] at hE
    exact (H 1 0 (by decide)).2 (by simp [hE])
  · rw [e1] at hE
    refine (H 0 2 (by decide)).2 ?_
    simp [← hE, pow_two]
  · rw [e2] at hE
    refine (H 2 0 (by decide)).2 ?_
    have hp : absPow k 1 = (u ^ 2)⁻¹ := by rw [hE, inv_inv]
    simp [hp, pow_two]
private theorem noLk_above (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal)
    (ha : IsLocalArtin h a) (hv : A.valuation (l : Ω) < 1) {m : ℕ} (hm : 2 ≤ m) {b : ℤ} {k : ℕ} (hk : 0 < k)
    {ω₀ ω₁ : (w.adicCompletion L)ˣ →* ℂˣ} {κ₀ κ₁ : Dec (F := L) A →* (Qbar l)ˣ}
    (h₀ : OrdChar ι a ω₀ (fun _ => -(b + m)) κ₀) (h₁ : OrdChar ι a ω₁ (fun _ => -b) κ₁)
    (hκ : ∀ s : ↥(Dec (F := L) A), (s : G L Ω) ∈ Ine (F := L) A →
      κ₀ s ^ k = (cycBar L Ω l s ^ (b + m)) ^ k ∧ κ₁ s ^ k = (cycBar L Ω l s ^ b) ^ k) :
    UpperTheory.V.Z.Sym.W.NoLk (ω₀ / ω₁) := by
  let u := ω₀ / ω₁
  let c : Fin 3 → ℤ := ![m, 0, -m]
  let ψ : Fin 3 → Dec (F := L) A →* (Qbar l)ˣ := ![κ₀ / κ₁, 1, κ₁ / κ₀]
  let hh : Fin 3 → (L →+* Qbar l) → ℤ := fun i _ => (![-(m : ℤ), 0, (m : ℤ)] : Fin 3 → ℤ) i
  have hq : ∀ {p q y : (Qbar l)ˣ} {e f : ℤ}, p ^ k = (y ^ e) ^ k → q ^ k = (y ^ f) ^ k →
      (p / q) ^ k = (y ^ (e - f)) ^ k := fun h1 h2 => by
    rw [div_pow, h1, h2, ← div_pow, zpow_sub, div_eq_mul_inv]
  have hp : ∀ (i : Fin 3) (s : ↥(Dec (F := L) A)), (s : G L Ω) ∈ Ine (F := L) A →
      ψ i s ^ k = (cycBar L Ω l s ^ c i) ^ k := fun i s hs => by
    obtain ⟨h1, h2⟩ := hκ s hs
    fin_cases i
    · have := hq h1 h2
      simpa [ψ, c] using this
    · simp [ψ, c]
    · have := hq h2 h1
      simpa [ψ, c] using this
  have hne : ∀ i j, ψ i ≠ ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype := fun i j => by
    refine not_link hv hk (hp i) (hp j) ?_
    fin_cases i <;> fin_cases j <;> simp [c] <;> omega
  have H0 : OrdChar ι a u (fun _ => -(m : ℤ)) (κ₀ / κ₁) := by
    have := ord_div h₀ h₁
    have e : ((fun _ => -(b + m)) - fun _ => -b : (L →+* Qbar l) → ℤ) = fun _ => -(m : ℤ) := by
      funext t
      simp
    rwa [e] at this
  have H1 : OrdChar ι a (1 : (w.adicCompletion L)ˣ →* ℂˣ) (fun _ => 0) (1 : Dec (F := L) A →* (Qbar l)ˣ) := by
    have := ord_div h₀ h₀
    rw [div_self', div_self', sub_self] at this
    exact this
  have H2 : OrdChar ι a u⁻¹ (fun _ => (m : ℤ)) (κ₁ / κ₀) := by
    have := ord_div h₁ h₀
    have e : ((fun _ => -b) - fun _ => -(b + m) : (L →+* Qbar l) → ℤ) = fun _ => (m : ℤ) := by
      funext t
      simp
    rw [e] at this
    rwa [show u⁻¹ = ω₁ / ω₀ from inv_div _ _]
  have hO : ∀ i, OrdChar ι a ((![u, 1, u⁻¹] : Fin 3 → (w.adicCompletion L)ˣ →* ℂˣ) i) (hh i) (ψ i) := fun i => by
    fin_cases i
    · exact H0
    · exact H1
    · exact H2
  have hmono : ∀ t : L →+* Qbar l, StrictMono fun j : Fin 3 => hh j t := fun t => by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> simp [hh] <;> omega
  exact noLk_of u (not_linked H ι hw ha hmono hO hne)
private theorem above' (P : _root_.UpperTheory.V.Af.Hypotheses') (hl : l ≠ 2) {n : ℕ} {ι : Qbar l ≃+* ℂ} {ρ : G L Ω →* GL (Fin n) (Qbar l)}
    {HT : (L →+* Qbar l) → Multiset ℤ} (hρ : Continuous ρ) (HG : HasHTAt ρ HT w) (h : IsPlaceOver A w)
    (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) {τ : SmIrr (GL (Fin n) (w.adicCompletion L))} (H : LocGlobT ι ρ w τ)
    {rc : IrrGL (w.adicCompletion L) → WD h} (hrc : IsRecT h rc)
    (hp : GlobalTheory.RoadU.PlainTor (IrrGL.of τ.ρ τ.smooth τ.irred)) (hg : Gd (rc (algNorm τ)))
    {hh : Fin n → (L →+* Qbar l) → ℤ} (hm : ∀ t, StrictMono fun j => hh j t) {ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ}
    (hψ : ∀ i, W.IsLocAlg h (ψ i) fun t => hh i (t.1.comp (algebraMap L _)))
    (hf : W.HasFlag (ρ.comp (Dec (F := L) A).subtype) ψ)
    (hne : ∀ i j, ψ i ≠ ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype) :
    ∃ (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a ∧
    (∃ ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, Nonempty (τ.ρ.Equiv (PS ω)) ∧ ∀ i, OrdChar ι a (ω i) (hh i) (ψ i)) ∧
    ∀ j : W.Emb l w, HT (j.1.comp (algebraMap L _)) = Finset.univ.val.map fun i => hh i (j.1.comp (algebraMap L _)) := by
  obtain ⟨a, ha⟩ : ∃ a, IsLocalArtin h a := by
    obtain ⟨a, ha, -⟩ := hrc
    exact ⟨a, ha⟩
  have hc : Continuous (ρ.comp (Dec (F := L) A).subtype) := hρ.comp continuous_subtype_val
  choose ω hω using fun i => (Loc.ordCharIff P.litN.aut.art h ι _ ha (hh i) (ψ i)).1.2 ⟨flag_cont' hc hf i, hψ i⟩
  have hD : DRat ι h (ρ.comp (Dec (F := L) A).subtype) HT fun s => (rc (algNorm τ)).charPol s := fun O _ _ _ Bw hj =>
    have h1 := HG A h O Bw hj
    ⟨h1.1, h1.2, fun s => by rw [((H A h rc hrc).2 O Bw hj hg).2]⟩
  have hD' := _root_.UpperTheory.V.Loc.flag_weil_deligne_of_literal_automorphy_n P.litN L Ω l hl ι n w hw A h _ ha _ hc _ ω ψ hω hf _ _ hD
  refine ⟨a, ha, ⟨ω, ?_, hω⟩, jumps_eq h hw hD hD'⟩
  have hs : IsSubquotient τ.ρ (PS ω) := by
    obtain ⟨O, _, _, _, Bw, hj⟩ := Af.exists_bridge (l := l) h hw
    exact _root_.UpperTheory.V.Z.Desc.W.pseudo_local_langlands_descent P.litN L Ω n w A h _ ha rc hrc τ hp ω (fun i => (hω i).smooth) fun s =>
      ((hD O Bw hj).2.2 s).symm.trans ((hD' O Bw hj).2.2 s)
  exact (_root_.UpperTheory.V.Hi.prin_series_irreducible_and_unique_subquotient P.litN _ n ω (fun i => (hω i).smooth)
    (not_linked P.litN.aut.art ι hw ha (fun t i j hij => hm t hij) hω hne)).2 _ τ.ρ τ.irred hs
end
end
theorem UpperTheory.V.Z.Sym.W.above_w_statement : _root_.UpperTheory.V.Z.Sym.W.AboveWAlt := by
  intro P L Ω _ _ _ _ _ l _ ι hl r hr m hm w hw HT hHT A h ⟨b, k, κ, hk, hf, hκ⟩ τ H hPT
  have hv : A.valuation (l : Ω) < 1 := by
    have := (h ((l : ℕ) : 𝓞 L)).2 hw
    simpa using this
  let c : Fin 2 → ℤ := ![b + m, b]
  have hκ' : ∀ (i : Fin 2) (s : ↥(Dec (F := L) A)), (s : G L Ω) ∈ Ine (F := L) A → κ i s ^ k = (cycBar L Ω l s ^ c i) ^ k := by
    intro i s hs
    fin_cases i
    · exact (hκ s hs).1
    · exact (hκ s hs).2
  have hcont : Continuous (r.comp (Dec (F := L) A).subtype) := hr.comp continuous_subtype_val
  have hfc : ∀ i, Continuous (κ i) := flag_cont' hcont hf
  have hmono : ∀ t : L →+* Qbar l, StrictMono fun j : Fin 2 => (fun (i : Fin 2) (_ : L →+* Qbar l) => -c i) j t := by
    intro t
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i
    simp [c]
    omega
  have hne : ∀ i j, κ i ≠ κ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype := by
    intro i j
    refine not_link hv hk (hκ' i) (hκ' j) ?_
    fin_cases i <;> fin_cases j <;> simp [c] <;> omega
  obtain ⟨rc, hrc⟩ := _root_.UpperTheory.V.Z.Win.exRec'_alt P.litN h
  have hg : Gd (rc (algNorm τ)) := UpperTheory.V.Z.Win.Gu.plainGd L Ω A w h rc hrc 2 τ hPT
  obtain ⟨a, ha, ⟨ω, he, hO⟩, hj⟩ := above' P hl hr hHT h hw H hrc hPT hg hmono
    (fun i => locAlg P.litN.aut.art h hw (κ i) (hfc i) hk (c i) (hκ' i)) hf hne
  refine ⟨⟨_, fun i => (hO i).smooth.mul (isSmoothChar_of_isUnram (isUnram_absPow _ _)), he, ?_⟩, -(b + m), fun j => ?_⟩
  · have := noLk_above P.litN.aut.art ι hw ha hv hm hk (hO 0) (hO 1) hκ
    simpa [mul_div_mul_right_eq_div] using this
  · rw [hj j]
    simp [c]
    rfl
end
end
end

