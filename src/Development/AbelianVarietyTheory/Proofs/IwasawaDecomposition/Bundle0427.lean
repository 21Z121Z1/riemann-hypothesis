import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0406
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0352
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0424
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0379
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0366
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0353
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0380
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0409
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0425
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0337

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalLevelData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

open Classical in

noncomputable def GlobalTheory.AutPart.jumpOf (a : ℕ) (z : ℂ) : ℤ :=
  if h : ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2 then -h.choose else 0

theorem GlobalTheory.AutPart.jumpOf_spec (a : ℕ) (z : ℂ) (h : ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2) :
    ((GlobalTheory.AutPart.jumpOf a z : ℤ) : ℂ) = -z + ((a : ℂ) - 1) / 2 := by
  unfold GlobalTheory.AutPart.jumpOf
  rw [dif_pos h]
  conv_rhs => rw [h.choose_spec]
  push_cast; ring

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem GlobalTheory.AutPart.exists_autSpec : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∃ (Y : LocAut X) (Cb : LocBC Y), Nonempty (AutSpec A M tp.tup Sp.iq Y Cb) := by
  intro hArt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh hψ big X T Sp
  classical
  choose ι hfin F hF using fun i : X.nd.Loc => GlobalTheory.T.algebraicModularForms_irreducible_decomposition D (X.nd.mu i) (X.nd.j i) (mlX M X i)
  have irr : ∀ i P, NG.IsIrrRep (mlX M X i).wt.ρ (F i P) := fun i => (hF i).1
  have hinj := fun i => (hF i).2.1
  have hsurj := fun i => (hF i).2.2.1
  have hne := fun i => (hF i).2.2.2.1
  have hind := fun i => (hF i).2.2.2.2.1
  have htop := fun i => (hF i).2.2.2.2.2
  obtain ⟨ptV, hptV⟩ : ∃ ptV : ∀ i, ι i → Option (X.nd.X i), ∀ i P x, ptV i P = some x ↔
      (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F i P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y) := by
    refine ⟨fun i P => if h : ∃ x, (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F i P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y) then some h.choose else none, fun i P x => ?_⟩
    dsimp only
    by_cases h : ∃ x, (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F i P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y)
    · rw [dif_pos h]
      constructor
      · rintro ⟨⟩; exact h.choose_spec
      · intro hx
        rw [GlobalTheory.T.galois_family_local_condition D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i _ (hne i P) _ _ h.choose_spec hx]
    · rw [dif_neg h]
      exact ⟨fun h' => absurd h' (by simp), fun hx => (h ⟨x, hx⟩).elim⟩
  have hpts := fun i => haveI := hfin i; GlobalTheory.T.galois_family_unramified_outside D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i (ι i) (F i) (irr i) (hinj i) (hsurj i) (hne i) (hind i) (htop i) (ptV i) (hptV i)
  choose μ hμc hμ using GlobalTheory.T.galois_family_crystalline_weights D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp
  choose κ hκ using GlobalTheory.T.galois_family_determinant D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp
  choose b hb using fun i : X.nd.Loc => GlobalTheory.algWt_contragredient D.host.E D.R.nV (mlX M X i).wt
  have hralg : ∀ {a} (π : D.naut.CG a) τ, D.naut.ralg π → ∀ z ∈ D.naut.infG π τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2 :=
    fun π τ h => ((D.naut.ralg_def π).1 h τ).2
  refine ⟨{
    iotaQ := Sp.iq
    iotaQC := fun i => (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i)))
    iota_LL := Sp.iq_LL
    iotaQ_alg := Sp.iq_alg
    muC := μ
    muC_csd := hμc
    AV := ι
    finAV := hfin
    ptV := ptV
    typeV := fun i P => ((NG.isoTyp (mlX M X i).wt.ρ (F i P)).comap (mlX M X i).real)
    typeV_ne := hne
    typeV_indep := hind
    typeV_top := htop
    pt_surj := fun i => (hpts i).1
    eig_dim := fun i => (hpts i).2
    locV := fun i P w => D.nbc.locAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F i P, irrS := irr i P }) w
    satV := fun i P w => D.nbc.satAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F i P, irrS := irr i P }) w
    locV_unr := fun i P w => haveI := hfin i; GlobalTheory.T.galois_family_irreducible D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i (ι i) (F i) (irr i) (hinj i) (hsurj i) (hne i) (hind i) (htop i) P w
    pt_loc := fun i P x hx w hw => haveI := hfin i; GlobalTheory.T.galois_family_trace_frobenius D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i (ι i) (F i) (irr i) (hinj i) (hsurj i) (hne i) (hind i) (htop i) (ptV i) (hptV i) P x hx w hw
    infWt := fun i => D.nbc.infW (X.nd.j i) (A.au.clsWt (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 (b i))
    locW := fun i σ w => A.row.locR σ w
    satW := fun i σ w => A.row.satR σ w
    lab_loc := fun i k σ v => A.row.lab_eq k σ v
    wdOf := fun i {a} r w => A.wd.wdOf (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_dim := fun i {a} r w => A.wd.wdOf_dim (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_unr := fun i {a} r w => A.wd.wdOf_unr (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_frob := fun i {a} r w => A.wd.wdOf_frob (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_ine := fun i {a} r w => A.wd.wdOf_ine (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_mono0 := fun i {a} r w => A.wd.wdOf_mono0 (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    IsCrysW := fun i {a} r w => A.wd.IsCrysW (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    IsPotCrysW := fun i {a} r w => A.wd.IsPotCrysW (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    IsdRW := fun i {a} r w => A.wd.IsdRW (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    jumpsW := fun i {a} r τ => A.wd.jumpsW (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r τ
    wdOf_unrL := fun i {a} r w => A.wd.wdOf_unrL (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_mono0L := fun i {a} r w => A.wd.wdOf_mono0L (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    jumpsInf := fun i {a} π τ => (D.naut.infG π ((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp τ)).map (GlobalTheory.AutPart.jumpOf a)
    locAutHodgeTateWeightsLevelZero := fun i τ => (D.nbc.infW (X.nd.j i) (A.au.clsWt (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 (b i))
      ((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp τ)).map (GlobalTheory.AutPart.jumpOf D.R.nV)
    jumpsInf_def := fun i {a} π τ h => by
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl fun z hz => GlobalTheory.AutPart.jumpOf_spec a z (hralg π _ h z hz)
    locAut_hodgeTateWeightsLevelZero_def := fun i τ => by
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl fun z hz => GlobalTheory.AutPart.jumpOf_spec _ z ((D.nbc.infW_alg _ _ _).2 z hz)
    chi_mu := fun i w hw => GlobalTheory.T.galois_family_hecke_compatible hArt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh hψ big X T Sp i (μ i) (hμc i) (hμ i) w hw
    kFbar := κ }, {
    embAV := fun i P => (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F i P, irrS := irr i P })
    embAV_inj := fun i P P' h => hinj i P P' ((A.au.iso _ _ _ _ _).1 h).2
    embAV_loc := fun _ _ _ => rfl
    embAV_sat := fun _ _ _ => rfl
    embAV_sph := fun i P w hw => haveI := hfin i; GlobalTheory.T.galois_family_polarized D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i (ι i) (F i) (irr i) (hinj i) (hsurj i) (hne i) (hind i) (htop i) P w hw
    embAV_inf := fun i P => by
      exact (congrArg (D.nbc.infW (X.nd.j i)) (A.au.wt _ _ _ _ (b i) (hb i).1)).symm }, ⟨{
    iotaQ := fun _ => rfl
    iotaQC := fun _ => rfl
    kFbar := hκ
    locW := fun _ _ _ => rfl
    satW := fun _ _ _ => rfl
    wdOf := fun _ _ _ _ => ⟨rfl, Iff.rfl, Iff.rfl, Iff.rfl, fun _ => rfl⟩
    muC := hμ
    S := F
    irr := irr
    inj := hinj
    surj := hsurj
    typeV := fun _ _ => rfl
    ptV := hptV
    emb := fun _ _ => rfl }⟩⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitHeckeOperatorInverseConjugatePlaceCosetSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeEigCoset

open GlobalTheory.LFun.ConjPlace

theorem heckeVec_Tj_inv_conj_eq_sum : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ (k : ℕ), k ≤ n →
    ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L), Continuous i →
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L)) V)
    (R : Finset (GAf L n)), (∀ γ ∈ R, γ ∈ tSet L n s ϖ k) → (∀ x ∈ tSet L n s ϖ k, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n) →
    ∀ e ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n),
      GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n)
                   (fun g => Formalism.UG.Tj ℂ n (Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w) (i ϖ) k g⁻¹) e =
        ∑ γ ∈ R, ρ (Matrix.GeneralLinearGroup.map i.toRingHom ((GlobalTheory.HeckeFrob.conjSplit s).loc n γ)) e := by
  intro L _ _ _ n s ϖ hϖ k hk i hi V _ _ ρ R hR1 hR2 e he
  classical
  have hO : ∀ a, i a ∈ Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w ↔
      a ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
    intro a
    have h := GlobalTheory.T.valued_le_one_iff_of_continuous_ringEquiv _ _ s.v (GlobalTheory.HeckeFrob.conjSplit s).w i hi a
    exact h.trans (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    have h0 : Valued.v (0 : s.v.adicCompletion (maximalRealSubfield L)) = WithZero.exp (-1 : ℤ) := hϖ
    rw [map_zero] at h0
    exact WithZero.exp_ne_zero h0.symm
  set ϖu : (s.v.adicCompletion (maximalRealSubfield L))ˣ := Units.mk0 ϖ hϖ0 with hϖu
  have ha : invT i n (dGL n ϖu k) = (dGL n (Units.map (i : _ →* _) ϖu) k)⁻¹ := by
    rw [← invT_dGL, map_inv, inv_inv]
  have h1 : (fun g => Formalism.UG.Tj ℂ n (Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w) (i ϖ) k g⁻¹) =
      Formalism.UG.dosetInd ℂ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n) (invT i n (dGL n ϖu k)) := by
    funext g
    have hiϖ : i ϖ = ((Units.map (i : s.v.adicCompletion (maximalRealSubfield L) →* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) ϖu :
        ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L)ˣ) : (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) := by
      rw [Units.coe_map, hϖu, Units.val_mk0]
      rfl
    rw [hiϖ, Tj_apply, Formalism.UG.dosetInd, Set.indicator_apply, Pi.one_apply]
    refine if_congr ?_ rfl rfl
    rw [DoubleCoset.mem_doubleCoset, ha]
    constructor
    · rintro ⟨x, hx, y, hy, h⟩
      exact ⟨y⁻¹, inv_mem hy, x⁻¹, inv_mem hx, by rw [← inv_inv g, h]; group⟩
    · rintro ⟨x, hx, y, hy, h⟩
      exact ⟨y⁻¹, inv_mem hy, x⁻¹, inv_mem hx, by rw [h]; group⟩
  have hK : ∀ x : GAf L n, TrivOutside {s.v} x → (x ∈ tSet L n s ϖ k ↔ invT i n (s.loc n x) ∈
      DoubleCoset.doubleCoset (invT i n (dGL n ϖu k)) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n : Set _)
        (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n)) := by
    intro x hx
    rw [tSet, Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨-, A, hA, B, hB, h⟩
      refine ⟨invT i n A, (mem_iff_invT i hO A).1 hA, invT i n B, (mem_iff_invT i hO B).1 hB, ?_⟩
      have : s.loc n x = A * dGL n ϖu k * B := Units.ext (by rw [Units.val_mul, Units.val_mul, h]; rfl)
      rw [this, map_mul, map_mul]
    · rintro ⟨A', hA', B', hB', h⟩
      obtain ⟨A, rfl⟩ := (invT i n).surjective A'
      obtain ⟨B, rfl⟩ := (invT i n).surjective B'
      rw [← map_mul, ← map_mul, (invT i n).apply_eq_iff_eq] at h
      refine ⟨hx, A, (mem_iff_invT i hO A).2 hA', B, (mem_iff_invT i hO B).2 hB', ?_⟩
      rw [h]
      rfl
  have hφK : ∀ x : GAf L n, TrivOutside {s.v} x →
      (invT i n (s.loc n x) ∈ GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n ↔ x ∈ Umax L n) :=
    fun x hx => (mem_iff_invT i hO _).symm.trans (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hx)
  have hRa : ∀ γ' ∈ R.image (fun γ => invT i n (s.loc n γ)), γ' ∈ DoubleCoset.doubleCoset (invT i n (dGL n ϖu k))
      (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n : Set _) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n) := by
    intro γ' hγ'
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hγ'
    exact (hK γ (hR1 γ hγ).1).1 (hR1 γ hγ)
  have hRb : ∀ g ∈ DoubleCoset.doubleCoset (invT i n (dGL n ϖu k))
      (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n : Set _) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n),
      ∃! γ', γ' ∈ R.image (fun γ => invT i n (s.loc n γ)) ∧ γ'⁻¹ * g ∈ GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n := by
    intro g hg
    obtain ⟨-, -, hlift⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
    obtain ⟨x, ⟨hx, hxg⟩, -⟩ := hlift ((invT i n).symm g)
    have hgx : g = invT i n (s.loc n x) := by rw [hxg]; simp
    have hxT : x ∈ tSet L n s ϖ k := (hK x hx).2 (hgx ▸ hg)
    obtain ⟨γ, ⟨hγ, hγx⟩, huniq⟩ := hR2 x hxT
    have key : ∀ δ ∈ R, (invT i n (s.loc n δ))⁻¹ * g ∈ GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n ↔
        δ⁻¹ * x ∈ Umax L n := by
      intro δ hδ
      rw [hgx, ← map_inv, ← map_inv, ← map_mul, ← map_mul]
      exact hφK _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hR1 δ hδ).1) hx)
    refine ⟨invT i n (s.loc n γ), ⟨Finset.mem_image_of_mem _ hγ, (key γ hγ).2 hγx⟩, ?_⟩
    rintro γ' ⟨hγ', hγ'g⟩
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ'
    rw [huniq δ ⟨hδ, (key δ hδ).1 hγ'g⟩]
  have hinj : Set.InjOn (fun γ => invT i n (s.loc n γ)) R := by
    intro γ₁ h₁ γ₂ h₂ heq
    have hγ₂ := hR1 γ₂ h₂
    obtain ⟨γ, -, huniq⟩ := hR2 γ₂ hγ₂
    have e1 : γ₁⁻¹ * γ₂ ∈ Umax L n := by
      rw [← hφK _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hR1 γ₁ h₁).1) hγ₂.1), map_mul, map_mul,
        map_inv, map_inv]
      simp only at heq
      rw [heq, inv_mul_cancel]
      exact one_mem _
    exact (huniq γ₁ ⟨h₁, e1⟩).trans (huniq γ₂ ⟨h₂, by rw [inv_mul_cancel]; exact one_mem _⟩).symm
  rw [h1, GlobalTheory.LFun.heckeVec_dosetInd he hRa hRb, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [GlobalTheory.HeckeEigConj.map_loc_conjSplit]

end GlobalTheory.HeckeEigCoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLieActionThroughWeylAlgebra
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.Mem.Lift.WeylAction

open GlobalTheory.RealWeil

section Mat

variable {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ}

omit [Fintype O] in
theorem blk_apply (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ) (k l : (Fin m × Fin n) × O) :
    blk b a k l = if k.2 = l.2 then b k.2 k.1.1 l.1.1 * a k.2 l.1.2 k.1.2 else 0 := rfl

theorem sum_blk {A : Type} [AddCommGroup A] [Module ℂ A] (b : O → Matrix (Fin m) (Fin m) ℂ)
    (a : O → Matrix (Fin n) (Fin n) ℂ) (τ : O) (h : ∀ τ', τ' ≠ τ → b τ' = 0 ∨ a τ' = 0)
    (y : (Fin m × Fin n) × O → (Fin m × Fin n) × O → A) :
    ∑ k, ∑ l, blk b a k l • y k l =
      ∑ p : Fin m × Fin n, ∑ q : Fin m × Fin n, (b τ p.1 q.1 * a τ q.2 p.2) • y (p, τ) (q, τ) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single τ _ (by simp)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [blk_apply, ite_smul]
  · intro τ' _ hτ
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases h τ' hτ with e | e <;> simp [blk_apply, e]

theorem sum_left {A : Type} [AddCommGroup A] [Module ℂ A] (X : Matrix (Fin m) (Fin m) ℂ) (τ : O)
    (y : (Fin m × Fin n) × O → (Fin m × Fin n) × O → A) :
    ∑ k, ∑ l, blk (Pi.single τ X) (fun _ => 1) k l • y k l =
      ∑ i, ∑ j, X i j • ∑ a, y ((i, a), τ) ((j, a), τ) := by
  rw [sum_blk _ _ τ fun τ' h => Or.inl (Pi.single_eq_of_ne h _)]
  simp only [Fintype.sum_prod_type, Pi.single_eq_same, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_smul,
    zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem sum_right {A : Type} [AddCommGroup A] [Module ℂ A] (Y : Matrix (Fin n) (Fin n) ℂ) (τ : O)
    (y : (Fin m × Fin n) × O → (Fin m × Fin n) × O → A) :
    ∑ k, ∑ l, blk (fun _ => 1) (Pi.single τ (-Y)) k l • y k l =
      ∑ a, ∑ b, Y a b • -∑ i, y ((i, b), τ) ((i, a), τ) := by
  rw [sum_blk _ _ τ fun τ' h => Or.inr (Pi.single_eq_of_ne h _)]
  have e : ∀ (i : Fin m) (b : Fin n), ∑ q : Fin m × Fin n, ((1 : Matrix (Fin m) (Fin m) ℂ) i q.1 * (-Y) q.2 b) •
      y ((i, b), τ) (q, τ) = ∑ a, -(Y a b • y ((i, b), τ) ((i, a), τ)) := by
    intro i b
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp [Matrix.one_apply, ite_smul]
  simp only [Pi.single_eq_same]
  rw [Fintype.sum_prod_type]
  simp only [e, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans Finset.sum_comm

end Mat

variable {D : D7} {θ : InfF D}

theorem hasDerivAt_comp (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (τ' : D.what₂.Tau) (i j : Fin V.rank) :
    HasDerivAt (fun t : ℝ => compAt θ τ' (Formalism.L2.Theta.mt V (oneP θ V τ X t)) i j)
      ((Pi.single τ X : D.what₂.Tau → _) τ' i j) 0 := by
  by_cases h : τ' = τ
  · subst h
    have e : ∀ t : ℝ, compAt θ τ' (Formalism.L2.Theta.mt V (oneP θ V τ' X t)) = NormedSpace.exp (t • X) :=
      fun t => (isAtTau_oneP hθ hX t).2.1
    have := hasDerivAt_exp_entry X 0 i j
    rw [zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at this
    simpa only [e, Pi.single_eq_same] using this
  · have e : ∀ t : ℝ, compAt θ τ' (Formalism.L2.Theta.mt V (oneP θ V τ X t)) = 1 :=
      fun t => (isAtTau_oneP hθ hX t).2.2 τ' h
    simp only [e, Pi.single_eq_of_ne h]
    exact hasDerivAt_const _ _

theorem oneP_inv (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (t : ℝ) : (oneP θ V τ X t)⁻¹ = oneP θ V τ (-X) t := by
  have : oneP θ V τ (-X) t = oneP θ V τ X (-t) := by
    unfold oneP
    rw [smul_neg, neg_smul]
  rw [this]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← oneP_add hθ hX, add_neg_cancel, oneP_zero hθ]

theorem neg_mem_lieAt {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : -X ∈ lieAt V τ := by
  have h : Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 := hX
  show (-X)ᴴ * gramAt D V τ + gramAt D V τ * (-X) = 0
  rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, h, neg_zero]

theorem weyl_action : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ θ : InfF D, IsInfFam θ → ∃ x d : D.what₂.Tau → Fin T.rank × Fin S.rank → Module.End ℂ (GlobalTheory.RealWeil.thetaSub ψ S T), ∀ τ, IsCCR (x τ) (d τ) ∧ (∀ X ∈ lieAt T τ, ∃ lam : ℂ, ∀ f g h, HasDerivAt (fun t : ℝ => thKer ψ S T om f g (h * oneP θ T τ X t)) (thKer ψ S T om ((∑ i, ∑ j, X i j • ∑ a, x τ (i, a) * d τ (j, a)) f + lam • f) g h) 0) ∧ ∀ Y ∈ lieAt S τ, ∃ lam : ℂ, ∀ f g h, HasDerivAt (fun t : ℝ => thKer ψ S T om f (g * oneP θ S τ Y t) h) (thKer ψ S T om ((∑ a, ∑ b, Y a b • -∑ i, x τ (i, b) * d τ (i, a)) f + lam • f) g h) 0 := by
  intro D ψ hψ S T om hw hc θ hθ
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨x, d, ⟨c1, c2, c3⟩, hn⟩ := GlobalTheory.T.exists_ccr_operators_thetaFunctions D θ σ h ψ hψ S T
  have key : ∀ γ : ℝ → GA D S × GA D T, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) →
      (∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) → ∀ X : Matrix (Ix S T) (Ix S T) ℂ,
      (∀ k l, HasDerivAt (fun t => mM θ S T (γ t) k l) (X k l) 0) → ∃ lam : ℂ, ∀ (f : thetaSub ψ S T) p,
      HasDerivAt (fun t => om (p * γ t) f.1 0) (om p ((∑ k, ∑ l, X k l • (x k * d l)) f + lam • f).1 0) 0 := by
    intro γ h1 h2 h3 X h4
    obtain ⟨lam, hl⟩ := GlobalTheory.T.hasDerivAt_weilRep_realOneParam_adelicPoint D θ σ h ψ hψ S T om hw hc γ h1 h2 h3 X h4
    refine ⟨lam, fun f p => ?_⟩
    have e := coe_toB hψ f.1 f.2
    have h5 := hl (toB hψ f.1 f.2) (e.symm ▸ f.2) p 0
    have e2 : ((∑ k, ∑ l, X k l • (x k * d l)) f + lam • f).1 =
        ((nOp (rhoV hψ σ S T) (HM S T) X (toB hψ f.1 f.2) + lam • toB hψ f.1 f.2).1 : WO S T → ℂ) := by
      rw [Submodule.coe_add, hn X f _ e]
      rfl
    rw [e2]
    exact h5
  refine ⟨fun τ k => x (k, τ), fun τ k => d (k, τ), fun τ => ⟨⟨fun k l => c1 _ _, fun k l => c2 _ _, fun k l => ?_⟩,
    fun X hX => ?_, fun Y hY => ?_⟩⟩
  · rw [c3]
    simp
  · obtain ⟨lam, hl⟩ := key (fun t => (1, oneP θ T τ X t)) (continuous_const.prodMk (continuous_oneP hθ hX))
      (fun s t => by rw [oneP_add hθ hX, Prod.mk_mul_mk, one_mul])
      (fun t => ⟨one_mem _, (isAtTau_oneP hθ hX t).1⟩) (blk (Pi.single τ X) fun _ => 1) (fun k l => by
        simp only [mM_apply, inv_one, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, blk_apply]
        split_ifs
        · exact (hasDerivAt_comp hθ hX _ _ _).mul_const _
        · exact hasDerivAt_const _ _)
    refine ⟨lam, fun f g k => ?_⟩
    have := hl f (g, k)
    rw [sum_left X τ fun k l => x k * d l] at this
    simp only [Prod.mk_mul_mk, mul_one] at this
    exact this
  · obtain ⟨lam, hl⟩ := key (fun t => (oneP θ S τ Y t, 1)) ((continuous_oneP hθ hY).prodMk continuous_const)
      (fun s t => by rw [oneP_add hθ hY, Prod.mk_mul_mk, one_mul])
      (fun t => ⟨(isAtTau_oneP hθ hY t).1, one_mem _⟩) (blk (fun _ => 1) (Pi.single τ (-Y))) (fun k l => by
        simp only [mM_apply, oneP_inv hθ hY, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, blk_apply]
        split_ifs
        · exact (hasDerivAt_comp hθ (neg_mem_lieAt hY) _ _ _).const_mul _
        · exact hasDerivAt_const _ _)
    refine ⟨lam, fun f g k => ?_⟩
    have := hl f (g, k)
    rw [sum_right Y τ fun k l => x k * d l] at this
    simp only [Prod.mk_mul_mk, mul_one] at this
    exact this

end GlobalTheory.Mem.Lift.WeylAction

end
end

