import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0728
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0730
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0201
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameRamifiedTypeAtPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0409
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.V0TLeISupEigenspace

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameLocIffHeckeCong
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.CoefDuty
set_option synthInstance.maxHeartbeats 400000 in
theorem sameLoc_iff_heckeCong_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L → ∀ (j : ℕ) (w : D.what₂.places.Pl) (i i' : L.X.nd.Loc), i ∈ L.X.nd.locs j w → i' ∈ L.X.nd.locs j w → ∀ (x : L.X.nd.X i) (x' : L.X.nd.X i'), (i = i' ↔ ∀ (v : PlE D.host) (k : ℕ), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) - iotaO L.X.nd L.Y.naut i' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x') ∈ (A.pl.plB w).nonunits) := by
  intro D cf jE A M C tup big L hB j w i i' hi hi' x x'
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hB
  have hiC : ∀ (a : L.X.nd.Loc) (ha : a ∈ L.X.nd.locs j w) (z : L.X.nd.O a),
      iotaO L.X.nd L.Y.naut a z = Sp.iotaC j w (Sp.phO j w a ha z) := by
    intro a ha z
    rw [← Sp.iotaC_coh j w a ha z]
    show ((L.Y.naut.iotaQC a).toRingHom.comp (L.Y.naut.iotaQ a)) (algebraMap _ _ z) = _
    rw [RingHom.comp_apply, Au.iotaQ, Au.iotaQC]
    rfl
  have key : ∀ (a : L.X.nd.Loc) (ha : a ∈ L.X.nd.locs j w) (y : L.X.nd.O a),
      iotaO L.X.nd L.Y.naut a y ∈ (A.pl.plB w).nonunits ↔ y ∈ IsLocalRing.maximalIdeal (L.X.nd.O a) := by
    intro a ha y
    have hw : L.X.nd.w a = w := ((L.X.nd.locs_mem j w a).1 ha).2
    subst hw
    obtain ⟨h, e⟩ := Au.kFbar a y
    rw [ValuationSubring.mem_nonunits_iff]
    have e1 : (A.pl.plB (L.X.nd.w a)).valuation (iotaO L.X.nd L.Y.naut a y) =
        (A.pl.plB (L.X.nd.w a)).valuation ((⟨_, h⟩ : A.pl.plB (L.X.nd.w a)) : ℂ) := rfl
    rw [e1, ← ValuationSubring.valuation_lt_one_iff, ← IsLocalRing.residue_eq_zero_iff,
      ← IsLocalRing.residue_eq_zero_iff, ← map_eq_zero (L.Y.naut.kFbar a), ← e]
    simp only [EmbeddingLike.map_eq_zero_iff]
  have gen : ∀ v k, GenAt D (D.what₂.places.resChar w) (C.Q w) v k ↔
      GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k := by
    intro v k; rw [Sp.Qc_eq]
  constructor
  · rintro rfl v k hvk
    have hvk' := (gen v k).1 hvk
    have e1 := Sp.ptX_hT j w i hi x v k hvk'
    have e2 := Sp.ptX_hT j w i hi' x' v k hvk'
    have hc : Formalism.L2.NCov.cls (Sp.ptX j w i hi x).1 = Formalism.L2.NCov.cls (Sp.ptX j w i hi' x').1 :=
      (Sp.ptX j w i hi x).2.1.trans (Sp.ptX j w i hi' x').2.1.symm
    generalize (Sp.ptX j w i hi x).1 = ψ at e1 hc
    generalize (Sp.ptX j w i hi' x').1 = ψ' at e2 hc
    generalize (⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk', rfl⟩⟩ : heckeAlg Sp.B j w) = t at e1 e2
    have hmem : t - algebraMap _ _ (ψ t) ∈ Formalism.L2.NCov.cls ψ' := by
      rw [← hc, Formalism.L2.NCov.cls, RingHom.mem_ker]
      change IsLocalRing.residue _ (ψ (t - algebraMap _ _ (ψ t))) = 0
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self, map_zero]
    rw [Formalism.L2.NCov.cls, RingHom.mem_ker] at hmem
    change IsLocalRing.residue _ (ψ' (t - algebraMap _ _ (ψ t))) = 0 at hmem
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, map_sub, sub_eq_zero, ← e1, ← e2] at hmem
    have r := GlobalTheory.PtLocalEig.residue_map_equiv (Sp.phO j w i hi).symm hmem
    simp only [RingEquiv.symm_apply_apply] at r
    rw [← map_sub]
    refine (key i hi _).2 ?_
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, r, sub_self]
  · intro H
    apply Sp.mx_inj j w hi hi'
    rw [← (Sp.ptX j w i hi x).2.1, ← (Sp.ptX j w i' hi' x').2.1]
    refine GlobalTheory.PtLocalEig.cls_eq_of_residue _ _ _ ?_
    rintro _ ⟨v, k, hvk, rfl⟩
    rw [← Sp.ptX_hT j w i hi x v k hvk, ← Sp.ptX_hT j w i' hi' x' v k hvk]
    have h1 := H v k ((gen v k).2 hvk)
    have hz : iotaO L.X.nd L.Y.naut i' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x') =
        iotaO L.X.nd L.Y.naut i ((Sp.phO j w i hi).symm
          (Sp.phO j w i' hi' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x'))) := by
      rw [hiC i hi, hiC i' hi', RingEquiv.apply_symm_apply]
    rw [hz, ← map_sub, key i hi, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at h1
    have h2 := GlobalTheory.PtLocalEig.residue_map_equiv (Sp.phO j w i hi) h1
    rwa [RingEquiv.apply_symm_apply] at h2
end GlobalTheory.CoefDuty
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitOutIffGenAt
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.PtExt
variable {D : D7}
theorem splitOut_iff_genAt_alt {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : MtFam D} {C : NChoice D}
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)}
    (hB : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L) {j : ℕ} {w : D.what₂.places.Pl} {i : L.X.nd.Loc}
    (hi : i ∈ L.X.nd.locs j w) (v : PlE D.host) (k : ℕ) :
    (SplitOut L.X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV) ↔ GenAt D (D.what₂.places.resChar w) (C.Q w) v k := by
  obtain ⟨Sp, -, -⟩ := hB
  have hw : L.X.nd.w i = w := ((L.X.nd.locs_mem j w i).1 hi).2
  have hl : L.X.nd.l i = D.what₂.places.resChar w := by rw [← hw]; exact (L.X.nd.w_l i).symm
  have hQ : L.X.nd.Q i = C.Q w := (Sp.Q_eq j w i hi).trans (Sp.Qc_eq j w)
  have hS : v ∈ L.X.nd.S i ↔ v ∈ placesS D (L.X.nd.l i) := L.X.nd.S_def i v
  unfold SplitOut GenAt
  rw [hS, ← hl, ← hQ]
  tauto
theorem sys_eq_iota_of_gen_at {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : MtFam D} {C : NChoice D}
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)}
    (hB : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L) {j : ℕ} {w : D.what₂.places.Pl} {i : L.X.nd.Loc}
    (hi : i ∈ L.X.nd.locs j w) (x : L.X.nd.X i) {v : PlE D.host} {k : ℕ}
    (h : GenAt D (D.what₂.places.resChar w) (C.Q w) v k) :
    sys L i x v k = iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) := by
  unfold sys
  rw [if_pos ((_root_.GlobalTheory.PtExt.splitOut_iff_genAt_alt hB hi v k).2 h)]
theorem sys_eq_zero_of_not_gen_at {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : MtFam D} {C : NChoice D}
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)}
    (hB : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L) {j : ℕ} {w : D.what₂.places.Pl} {i : L.X.nd.Loc}
    (hi : i ∈ L.X.nd.locs j w) (x : L.X.nd.X i) {v : PlE D.host} {k : ℕ}
    (h : ¬ GenAt D (D.what₂.places.resChar w) (C.Q w) v k) : sys L i x v k = 0 := by
  unfold sys
  rw [if_neg (fun h' => h ((_root_.GlobalTheory.PtExt.splitOut_iff_genAt_alt hB hi v k).1 h'))]
theorem sys_mem_eig_set_of_built {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : MtFam D} {C : NChoice D}
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)}
    (hB : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L) {j : ℕ} {w : D.what₂.places.Pl} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {i : L.X.nd.Loc}
    (hi : i ∈ L.X.nd.locs j w) (x : L.X.nd.X i) :
    sys L i x ∈ EigSet (M (D.what₂.muTw w) j h1 h2) (D.what₂.places.resChar w) (C.Q w) := by
  refine ⟨fun v k h => _root_.GlobalTheory.PtExt.sys_eq_zero_of_not_gen_at hB hi x h, ?_⟩
  have hB' := hB
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hB'
  obtain ⟨hj, hw⟩ := (L.X.nd.locs_mem j w i).1 hi
  subst hj hw
  obtain ⟨P, hP⟩ := L.Y.naut.pt_surj i x
  have key : ∃ y : D.what₂.Mt (L.X.nd.mu i) (L.X.nd.j i), y ≠ 0 ∧
      ∀ (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
        GenAt D (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i)) v k → IsConjPl D.host v s.w →
        IsUnif D.host.E s.v ϖ →
        NG.tN (M (L.X.nd.mu i) (L.X.nd.j i) h1 h2).J s ϖ k ((M (L.X.nd.mu i) (L.X.nd.j i) h1 h2).real y) =
          sys L i x v k • (M (L.X.nd.mu i) (L.X.nd.j i) h1 h2).real y := by
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (L.Y.naut.typeV_ne i P)
    refine ⟨y, hy0, fun v k s ϖ hg hc hu => ?_⟩
    obtain ⟨hso, k1, k2⟩ := (_root_.GlobalTheory.PtExt.splitOut_iff_genAt_alt hB hi v k).2 hg
    rw [_root_.GlobalTheory.PtExt.sys_eq_iota_of_gen_at hB hi x hg]
    exact (Au.ptV i P x).1 hP v k s ϖ hso hc hu k1 k2 y hy
  rw [L.X.nd.mu_w i] at key
  exact key
end GlobalTheory.PtExt
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitOutOf
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
namespace GlobalTheory.ExtTheta
variable {D : D7}
theorem transport_alt (U : _root_.GlobalTheory.HeightCounting.AUSideAlt D) (M : MtFam D) {μ₀ μ₁ : D.what₂.Tup} {j₀ j₁ : ℕ} (hμ : μ₀ = μ₁) (hj : j₀ = j₁)
    (a₀ : 1 ≤ j₀) (b₀ : j₀ ≤ D.R.m) (a₁ : 1 ≤ j₁) (b₁ : j₁ ≤ D.R.m) {ι : Type}
    (S₀ : ι → Submodule ℂ (GAf D.host.E D.R.nV → (M μ₀ j₀ a₀ b₀).wt.W))
    (irr₀ : ∀ P, NG.IsIrrRep (M μ₀ j₀ a₀ b₀).wt.ρ (S₀ P))
    (surj : ∀ S', NG.IsIrrRep (M μ₀ j₀ a₀ b₀).wt.ρ S' →
      (NG.isoTyp (M μ₀ j₀ a₀ b₀).wt.ρ S').comap (M μ₀ j₀ a₀ b₀).real ≠ ⊥ → ∃ P, NG.IsoRep (S₀ P) S')
    (S₁ : Submodule ℂ (GAf D.host.E D.R.nV → (M μ₁ j₁ a₁ b₁).wt.W))
    (irr₁ : NG.IsIrrRep (M μ₁ j₁ a₁ b₁).wt.ρ S₁)
    (ne : (NG.isoTyp (M μ₁ j₁ a₁ b₁).wt.ρ S₁).comap (M μ₁ j₁ a₁ b₁).real ≠ ⊥) :
    ∃ P, (∀ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ) (c : ℂ),
      (∀ y ∈ (NG.isoTyp (M μ₁ j₁ a₁ b₁).wt.ρ S₁).comap (M μ₁ j₁ a₁ b₁).real,
        NG.tN (M μ₁ j₁ a₁ b₁).J s ϖ k ((M μ₁ j₁ a₁ b₁).real y) = c • (M μ₁ j₁ a₁ b₁).real y) →
      ∀ y ∈ (NG.isoTyp (M μ₀ j₀ a₀ b₀).wt.ρ (S₀ P)).comap (M μ₀ j₀ a₀ b₀).real,
        NG.tN (M μ₀ j₀ a₀ b₀).J s ϖ k ((M μ₀ j₀ a₀ b₀).real y) = c • (M μ₀ j₀ a₀ b₀).real y) ∧
      (∀ w, D.nbc.locAU j₀ (U.cls j₀ a₀ b₀ { (M μ₀ j₀ a₀ b₀).wt with S := S₀ P, irrS := irr₀ P }) w =
        D.nbc.locAU j₁ (U.cls j₁ a₁ b₁ { (M μ₁ j₁ a₁ b₁).wt with S := S₁, irrS := irr₁ }) w) ∧
      (∀ w, D.nbc.satAU j₀ (U.cls j₀ a₀ b₀ { (M μ₀ j₀ a₀ b₀).wt with S := S₀ P, irrS := irr₀ P }) w =
        D.nbc.satAU j₁ (U.cls j₁ a₁ b₁ { (M μ₁ j₁ a₁ b₁).wt with S := S₁, irrS := irr₁ }) w) ∧
      D.nbc.infW j₀ (D.nbc.wtAU j₀ (U.cls j₀ a₀ b₀ { (M μ₀ j₀ a₀ b₀).wt with S := S₀ P, irrS := irr₀ P })) =
        D.nbc.infW j₁ (D.nbc.wtAU j₁ (U.cls j₁ a₁ b₁ { (M μ₁ j₁ a₁ b₁).wt with S := S₁, irrS := irr₁ })) := by
  subst hμ; subst hj
  obtain ⟨P, hP⟩ := surj S₁ irr₁ ne
  have e := isoTyp_congr (M μ₀ j₀ a₀ b₀).wt.ρ (irr₀ P).1.stable hP
  have hc : U.cls j₀ a₀ b₀ { (M μ₀ j₀ a₀ b₀).wt with S := S₀ P, irrS := irr₀ P } =
      U.cls j₀ a₀ b₀ { (M μ₀ j₀ a₀ b₀).wt with S := S₁, irrS := irr₁ } :=
    (U.iso j₀ a₀ b₀ _ _).2 ⟨NG.AlgWt.Iso.refl _, hP⟩
  refine ⟨P, fun s ϖ k c h => ?_, fun w => ?_, fun w => ?_, ?_⟩
  · rw [e]; exact h
  · rw [hc]
  · rw [hc]
  · rw [hc]
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : MtFam D} {C : NChoice D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E}
theorem split_out_of_w_eq {big₀ big₁ : D.what₂.places.Pl → Finset ℂ} {X₀ X₁ : LocNd (lay0 D)} {T₀ : LocTw X₀} {T₁ : LocTw X₁}
    (Sp₀ : NdSpec A.pl M C big₀ X₀ T₀) (Sp₁ : NdSpec A.pl M C big₁ X₁ T₁) (i₀ : X₀.nd.Loc) (i₁ : X₁.nd.Loc)
    (hw : X₀.nd.w i₀ = X₁.nd.w i₁) (v : PlE D.host) (h : SplitOut X₀.nd i₀ v) : SplitOut X₁.nd i₁ v := by
  have hl : X₀.nd.l i₀ = X₁.nd.l i₁ := by rw [← X₀.nd.w_l, ← X₁.nd.w_l, hw]
  have q₀ : X₀.nd.Q i₀ = C.Q (X₀.nd.w i₀) :=
    (Sp₀.Q_eq _ _ i₀ ((X₀.nd.locs_mem _ _ _).2 ⟨rfl, rfl⟩)).trans (Sp₀.Qc_eq _ _)
  have q₁ : X₁.nd.Q i₁ = C.Q (X₁.nd.w i₁) :=
    (Sp₁.Q_eq _ _ i₁ ((X₁.nd.locs_mem _ _ _).2 ⟨rfl, rfl⟩)).trans (Sp₁.Qc_eq _ _)
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, hl ▸ h2, fun hs => h3 ?_, ?_⟩
  · have := (X₁.S_def i₁ v).1 hs
    refine (X₀.S_def i₀ v).2 ?_
    have hl' : X₀.l i₀ = X₁.l i₁ := hl
    rw [hl']; exact this
  · rw [q₁, ← hw, ← q₀]; exact h4
theorem mu_c_eq_of_mu_eq_of_j_eq {X₀ X₁ : LocNd (lay0 D)} {iq₀ : ∀ i : X₀.nd.Loc, FractionRing (X₀.nd.O i) →+* Qbar (X₀.nd.l i)}
    {iq₁ : ∀ i : X₁.nd.Loc, FractionRing (X₁.nd.O i) →+* Qbar (X₁.nd.l i)} {Y₀ : LocAut X₀} {Y₁ : LocAut X₁}
    {C₀ : LocBC Y₀} {C₁ : LocBC Y₁} (U₀ : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup iq₀ Y₀ C₀) (U₁ : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup iq₁ Y₁ C₁)
    (i₀ : X₀.nd.Loc) (i₁ : X₁.nd.Loc) (hμ : X₀.nd.mu i₀ = X₁.nd.mu i₁) (hj : X₀.nd.j i₀ = X₁.nd.j i₁) :
    (Y₀.muC i₀ : D.naut.CG 1) = Y₁.muC i₁ := by
  have hr := X₀.nd.j_range i₀
  let j : Fin D.R.m := ⟨X₀.nd.j i₀ - 1, by omega⟩
  have e₀ : j.1 + 1 = X₀.nd.j i₀ := by simp only [j]; omega
  have h₀ := U₀.muC i₀ j e₀
  have h₁ := U₁.muC i₁ j (e₀.trans hj)
  apply A.chr.e1.injective
  apply Subtype.ext
  rw [h₀, h₁, hμ]
set_option maxHeartbeats 1000000 in
theorem zn_of_alt {X₀ X₁ : LocNd (lay0 D)} {iq₀ : ∀ i : X₀.nd.Loc, FractionRing (X₀.nd.O i) →+* Qbar (X₀.nd.l i)}
    {iq₁ : ∀ i : X₁.nd.Loc, FractionRing (X₁.nd.O i) →+* Qbar (X₁.nd.l i)} {Y₀ : LocAut X₀} {Y₁ : LocAut X₁}
    {C₀ : LocBC Y₀} {C₁ : LocBC Y₁} (U₀ : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup iq₀ Y₀ C₀) (U₁ : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup iq₁ Y₁ C₁)
    (i₀ : X₀.nd.Loc) (i₁ : X₁.nd.Loc) (hw : X₀.nd.w i₀ = X₁.nd.w i₁) (hj : X₀.nd.j i₀ = X₁.nd.j i₁)
    (hs : ∀ v, SplitOut X₀.nd i₀ v → SplitOut X₁.nd i₁ v) (x₀ : X₀.nd.X i₀) (x₁ : X₁.nd.X i₁)
    (he : ∀ v k, SplitOut X₀.nd i₀ v → 1 ≤ k → k ≤ D.R.nV →
      iotaO X₁.nd Y₁.naut i₁ ((X₁.nd.hT i₁ v k : X₁.nd.X i₁ → X₁.nd.O i₁) x₁) =
        iotaO X₀.nd Y₀.naut i₀ ((X₀.nd.hT i₀ v k : X₀.nd.X i₀ → X₀.nd.O i₀) x₀))
    (h : x₁ ∈ ZN X₁.nd Y₁.naut i₁) : x₀ ∈ ZN X₀.nd Y₀.naut i₀ := by
  have hμ : X₀.nd.mu i₀ = X₁.nd.mu i₁ := by rw [X₀.nd.mu_w, X₁.nd.mu_w, hw]
  have hm := _root_.GlobalTheory.ExtTheta.mu_c_eq_of_mu_eq_of_j_eq U₀ U₁ i₀ i₁ hμ hj
  obtain ⟨P₁, hP₁, Pa, ⟨c1, c2, c3, c4, c5, c6⟩, hmem⟩ := h
  have ne := Y₁.naut.typeV_ne i₁ P₁
  rw [U₁.typeV] at ne
  obtain ⟨P₀, t1, t2, t3, t4⟩ := _root_.GlobalTheory.ExtTheta.transport_alt A.au M hμ hj (X₀.nd.j_range i₀).1 (X₀.nd.j_range i₀).2 (X₁.nd.j_range i₁).1
    (X₁.nd.j_range i₁).2 (U₀.S i₀) (U₀.irr i₀) (U₀.surj i₀) (U₁.S i₁ P₁) (U₁.irr i₁ P₁) ne
  have l1 : ∀ w, (Y₀.naut.locV i₀ P₀ w : D.naut.LP w) = Y₁.naut.locV i₁ P₁ w := fun w => by
    rw [C₀.embAV_loc, C₁.embAV_loc, U₀.emb, U₁.emb]; exact t2 w
  have l2 : ∀ w, Y₀.naut.satV i₀ P₀ w = Y₁.naut.satV i₁ P₁ w := fun w => by
    rw [C₀.embAV_sat, C₁.embAV_sat, U₀.emb, U₁.emb]; exact t3 w
  have l3 : Y₀.naut.infWt i₀ = Y₁.naut.infWt i₁ := by
    rw [C₀.embAV_inf i₀ P₀, C₁.embAV_inf i₁ P₁, U₀.emb, U₁.emb]; exact t4
  refine ⟨P₀, (U₀.ptV i₀ P₀ x₀).2 fun w k s ϖ h1 h2 h3 h4 h5 => ?_, Pa, ⟨c1, c2, c3, fun w hw => ?_, fun w hw => ?_, fun τ => ?_⟩, ?_⟩
  · have h6 := (U₁.ptV i₁ P₁ x₁).1 hP₁ w k s ϖ (hs w h1) h2 h3 h4 h5
    rw [U₁.typeV, he w k h1 h4 h5] at h6
    rw [U₀.typeV]
    exact t1 s ϖ k _ h6
  · exact (c4 w hw).trans (l1 w).symm
  · rw [l2]; exact c5 w hw
  · rw [l3]; exact c6 τ
  · have : (Y₀.naut.muC i₀ : D.naut.CG 1) = Y₁.naut.muC i₁ := hm
    rw [this]; exact hmem
set_option maxHeartbeats 1000000 in
theorem theta_loci_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ big₁ : D.what₂.places.Pl → Finset ℂ) (L₀ L₁ : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₀ L₀ → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ → ∀ (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc), L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ → L₀.lay.fixZ.nd.j i₀ = L₁.lay.fixZ.nd.j i₁ → ∀ e : L₁.lay.fixZ.nd.X i₁ ≃ L₀.lay.fixZ.nd.X i₀, (∀ (v : PlE D.host) (k : ℕ) (x : L₁.lay.fixZ.nd.X i₁), SplitOut L₁.lay.fixZ.nd i₁ v → 1 ≤ k → k ≤ D.R.nV → iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ ((L₁.lay.fixZ.nd.hT i₁ v k : L₁.lay.fixZ.nd.X i₁ → L₁.lay.fixZ.nd.O i₁) x) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ ((L₀.lay.fixZ.nd.hT i₀ v k : L₀.lay.fixZ.nd.X i₀ → L₀.lay.fixZ.nd.O i₀) (e x))) → ∀ x, x ∈ L₁.lay.fixZ.nd.Z i₁ ↔ e x ∈ L₀.lay.fixZ.nd.Z i₀ := by
  intro _ D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ _ _ _ big₀ big₁ L₀ L₁ ⟨Sp₀, ⟨U₀⟩, _⟩ ⟨Sp₁, ⟨U₁⟩, _⟩ i₀ i₁ hw hj e he x
  have s01 := _root_.GlobalTheory.ExtTheta.split_out_of_w_eq Sp₀ Sp₁ i₀ i₁ hw
  have s10 := _root_.GlobalTheory.ExtTheta.split_out_of_w_eq Sp₁ Sp₀ i₁ i₀ hw.symm
  refine (L₁.lay.zOk_fixZ.1 i₁ x).trans (Iff.trans ⟨fun h => ?_, fun h => ?_⟩ (L₀.lay.zOk_fixZ.1 i₀ (e x)).symm)
  · exact _root_.GlobalTheory.ExtTheta.zn_of_alt U₀ U₁ i₀ i₁ hw hj s01 (e x) x (fun v k h1 h2 h3 => he v k x (s01 v h1) h2 h3) h
  · exact _root_.GlobalTheory.ExtTheta.zn_of_alt U₁ U₀ i₁ i₀ hw.symm hj.symm s10 x (e x) (fun v k h1 h2 h3 => (he v k x h1 h2 h3).symm) h
end GlobalTheory.ExtTheta
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeOrthOfPin
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ThetaExh
theorem typeOrth_of_pin_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, MtForm D P.M i → GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i := by
  intro hL D P i hF
  obtain ⟨B, hB, hinner⟩ := hF
  exact GlobalTheory.ThetaExh.typeOrth_of_avTied D P.M P.H.av i B hB hinner
    (GlobalTheory.AlgFormsFin.finiteDimensional_forms D D.R.nV (P.M.loc i).wt (GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel D.host.E D.R.nV))
end GlobalTheory.ThetaExh
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeTameOfRamified
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TypeTame
theorem typeTame_of_ramified_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ i w hw, (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → GlobalTheory.SplitWeil.IsTame (S i w hw).mu → ¬ GlobalTheory.SplitWeil.IsUnram (S i w hw).mu → TypeTame S i w hw := by
  intro hL D P S hT i w hw hg htame hram
  refine ⟨htame, hram, fun Q => ?_⟩
  obtain ⟨h1, h2⟩ := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hcomp := hT.mu i w hw j hj
  obtain ⟨v, hov, hvq⟩ := GlobalTheory.T.exists_realSubfield_place_in_ramified_set D _ w hg (GlobalTheory.T.heckeChar_ramified_of_ramified_localComponent _ _ w _ hcomp hram)
  obtain ⟨s, ξ, hsv, hcs, hlp⟩ := P.H.level.para i j hj v hvq
  obtain ⟨f, hfI, hfT, hf0⟩ : ∃ f, f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) ∧
      f ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ ∧ f ≠ 0 := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i Q)
    rw [P.H.av.typeV] at hy
    refine ⟨(P.M.loc i).real y, hy, ?_, ?_⟩
    · rw [← (P.M.loc i).real_range]; exact ⟨y, rfl⟩
    · intro h; exact hy0 ((P.M.loc i).real_inj (h.trans (map_zero _).symm))
  obtain ⟨K, θ, hKm, hθ, hKi, hθo, hχθ⟩ := GlobalTheory.T.exists_splitPlaceParahoric_subgroup_character _ _ s D.R.r _ _ ξ hlp hcs.1
  have hfK : ∀ κ, TrivOutside {s.v} κ → ∀ h : s.loc D.R.nV κ ∈ K,
      NG.rt D.host.E D.R.nV κ f = ((θ ⟨s.loc D.R.nV κ, h⟩ : ℂˣ) : ℂ) • f := by
    intro κ hκ h
    have hJ : κ ∈ (P.M.loc i).J := (hlp.mem κ hκ).2 ((hKm _).1 h)
    rw [← hχθ κ hκ hJ h]
    exact hfT.2 ⟨κ, hJ⟩
  have hmu_eq : ∀ g (hg : NG.ParaRT s D.R.r g) (d : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ),
      (d : s.v.adicCompletion (maximalRealSubfield D.host.E)) = NG.detDD s D.R.r g →
      θ ⟨g, (hKm g).2 hg⟩ = ξ d := fun g hg d hd => hθ g _ d hd
  rcases GlobalTheory.T.eq_or_isConjPlace_of_over_splitPlace D s w (hsv ▸ hov) with hsw | hconj
  · subst hsw
    obtain ⟨c, T, hc, hci, -⟩ := hT.rep i s hw Q
    obtain ⟨u, hu0, hu⟩ := GlobalTheory.T.exists_localComponent_eigenvector_at_splitPlace_isotypic _ _ (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s _ (hT.rep i s hw Q) c hc hci
      K θ hKi hθo f hfI hf0 hfK
    refine ⟨u, hu0, GlobalTheory.T.isParahoricTypeVector_of_upperParahoric_eigen _ s D.R.r D.R.t _ ξ _ c hc hci hcomp.1 hcs.1 (fun k => (hcs.2 k).trans (hcomp.2 k).symm) u ?_⟩
    intro g hg d hd
    rw [← hmu_eq g hg d hd]
    exact hu g _
  · obtain ⟨hw', hci'⟩ := GlobalTheory.T.conjugateSplitPlace_eq_conjugatePlace_and_embedding D s w hconj
    subst hw'
    obtain ⟨c, T, hc, hci, -⟩ := hT.rep i (GlobalTheory.TypeTame.conjSP s) hw Q
    obtain ⟨K', θ', hK'i, hθ'o, hK'iff, hθ'eq, hK'of⟩ := GlobalTheory.T.exists_level_character_at_conjugateSplitPlace _ _ s K θ hKi hθo
    have hfK' : ∀ κ, TrivOutside {(GlobalTheory.TypeTame.conjSP s).v} κ → ∀ h' : (GlobalTheory.TypeTame.conjSP s).loc D.R.nV κ ∈ K',
        NG.rt D.host.E D.R.nV κ f = ((θ' ⟨(GlobalTheory.TypeTame.conjSP s).loc D.R.nV κ, h'⟩ : ℂˣ) : ℂ) • f := by
      intro κ hκ h'
      have h := (hK'iff κ).1 h'
      rw [hθ'eq κ h h']
      exact hfK κ hκ h
    obtain ⟨u, hu0, hu⟩ := GlobalTheory.T.exists_localComponent_eigenvector_at_splitPlace_isotypic _ _ (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) (GlobalTheory.TypeTame.conjSP s) _
      (hT.rep i (GlobalTheory.TypeTame.conjSP s) hw Q) c hc hci K' θ' hK'i hθ'o f hfI hf0 hfK'
    have hcsd : IsCSD D.host (P.tp.tup (D.nd.mu i) j) := by
      rw [← P.chr.muC i j hj]; exact (P.chr.csd _).1 (D.naut.muC_csd i)
    refine GlobalTheory.T.exists_parahoricType_vector_at_conjugate_place _ (GlobalTheory.TypeTame.conjSP s) D.R.r D.R.t _ ξ _ c hc hci hcomp.1 htame hcs.1 ?_ u hu0 ?_
    · intro k
      have e : Units.map ((GlobalTheory.TypeTame.conjSP s).i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E)) k =
          Units.map (s.i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E))
            (Units.map (MonoidHomClass.toMonoidHom D.host.conj) k) := by
        ext; simp [hci']
      have e2 := hcs.2 (Units.map (MonoidHomClass.toMonoidHom D.host.conj) k)
      have e3 := hcsd.1 _ _ hconj k
      have e4 := hcomp.2 k
      rw [e, e2, e3, e4]
    · intro g h hg hh d hd
      obtain ⟨h', e⟩ := hK'of g ((hKm g).2 hg) h hh
      rw [← hmu_eq g hg d hd, ← e]
      exact hu h h'
end GlobalTheory.TypeTame
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeVecBlockCharFixedPlace
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
open Filter Topology
namespace GlobalTheory.TypeBlockFix
variable {F : Type} [Field F] [NumberField F] {F' : Type} [Field F'] [NumberField F']
section loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end loc
end GlobalTheory.TypeBlockFix
namespace GlobalTheory.TypeBlockFix
open ValuativeRel
end GlobalTheory.TypeBlockFix
namespace GlobalTheory.TypeBlockFix
open Filter Topology
end GlobalTheory.TypeBlockFix
open GlobalTheory.TypeBlockFix in
theorem GlobalTheory.typeVec_blockChar_fixedPlace_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = D.naut.plGw k v → IsTame (S i s.w hw).mu → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ Q, ∃ f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), f ≠ 0 ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x f = blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • f := by
  intro hL D P S hS i k v s hw hsw _hT c hc hci Q
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i :=
    ⟨⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, by have := D.nd.j_range i; simp; omega⟩
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (D.naut.typeV_ne i Q)
  rw [P.H.av.typeV] at hy
  have hfT : (P.M.loc i).real y ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]; exact ⟨y, rfl⟩
  refine ⟨(P.M.loc i).real y, hy, fun h0 => hy0 ((P.M.loc i).real_inj (h0.trans (map_zero _).symm)), ?_⟩
  obtain ⟨ψ₀, ξ, hψ, hξ, hLv⟩ := P.H.level.uni i j hj k v s hsw
  intro x hx hblk
  set G := s.loc D.R.nV x with hG
  set h := Matrix.GeneralLinearGroup.map c.toRingHom G with hh
  have hent : ∀ a b, h.val a b = c (G.val a b) := fun a b => rfl
  have hient : ∀ a b, (h⁻¹).val a b = c ((G⁻¹).val a b) := by
    intro a b; rw [hh, ← map_inv]; rfl
  have hle : ∀ y, ValuativeRel.valuation _ (c y) ≤ 1 → Valued.v y ≤ 1 := fun y hy' =>
    (v_map_le_one_iff _ _ c hc y).1 ((complRel_le_one _ _).1 hy')
  have hlt : ∀ y, ValuativeRel.valuation _ (c y) < 1 → Valued.v y < 1 := fun y hy' =>
    (v_map_lt_one_iff _ _ c hc y).1 ((complRel_lt_one _ _).1 hy')
  have hI : ∀ a b, Valued.v (G.val a b) ≤ 1 := fun a b =>
    hle _ (by rw [← hent]; exact GlobalTheory.BlockType.val_le_one_of_mem_KO hblk.1 a b)
  have hI' : ∀ a b, Valued.v ((G⁻¹).val a b) ≤ 1 := fun a b =>
    hle _ (by rw [← hient]; exact GlobalTheory.BlockType.val_le_one_of_mem_KO ((KO _ _).inv_mem hblk.1) a b)
  have hcol : ∀ a (b : Fin D.R.nV), b.val < D.R.r → a ≠ b → Valued.v (G.val a b) < 1 := by
    intro a b hb hab
    refine hlt _ ?_
    have := hblk.2 a ⟨b.val, hb⟩
    rw [← hent]
    have e : b = Fin.castAdd D.R.t ⟨b.val, hb⟩ := Fin.ext rfl
    rw [← e] at this
    change ValuativeRel.valuation _ (h.val a b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) _) a b) < 1 at this
    rw [Matrix.one_apply_ne hab, sub_zero] at this
    exact this
  have hdiag : ∀ (b : Fin D.R.nV), b.val < D.R.r → Valued.v (G.val b b - 1) < 1 := by
    intro b hb
    refine hlt _ ?_
    have := hblk.2 b ⟨b.val, hb⟩
    have e : b = Fin.castAdd D.R.t ⟨b.val, hb⟩ := Fin.ext rfl
    rw [← e] at this
    change ValuativeRel.valuation _ (h.val b b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) _) b b) < 1 at this
    rw [Matrix.one_apply_eq, hent] at this
    rwa [map_sub, map_one]
  have hpara : NG.ParaRT s D.R.r G := by
    refine ⟨mem_GLint_of_entries _ G (fun a b => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hI a b))
      (fun a b => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hI' a b)), ?_⟩
    · intro a b ha hb
      exact hcol a b hb (fun e => by rw [e] at ha; omega)
  have huni : NG.UniRT s D.R.r G := by
    refine ⟨hpara, fun a b ha hb => ⟨fun hab => hcol a b hb (fun e => by rw [e] at hab; omega), fun e => ?_⟩⟩
    subst e; exact hdiag a ha
  have hmem : x ∈ (P.M.loc i).J := (hLv.mem x hx).2 huni
  have hcdet : c (NG.detDD s D.R.r G) = (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det := by
    let e : Fin D.R.t ≃ {a : Fin D.R.nV // D.R.r ≤ a.val} :=
      { toFun := fun b => ⟨Fin.natAdd D.R.r b, by simp⟩
        invFun := fun a => ⟨a.1.val - D.R.r, by have h1 : a.1.val < D.R.r + D.R.t := a.1.2; omega⟩
        left_inv := fun b => by ext; simp
        right_inv := fun a => by ext; simp; have := a.2; omega }
    rw [NG.detDD, show c (Matrix.of fun a b : {x : Fin D.R.nV // D.R.r ≤ x.val} => G.val a.1 b.1).det =
      c.toRingHom (Matrix.of fun a b : {x : Fin D.R.nV // D.R.r ≤ x.val} => G.val a.1 b.1).det from rfl,
      RingHom.map_det, ← Matrix.det_submatrix_equiv_self e]
    congr 1
  have hdet : NG.detDD s D.R.r G ≠ 0 := by
    intro h0
    exact (det_ne_zero_of_mem_blockGrp _ _ _ _ hblk) (hcdet.symm.trans (by rw [h0, map_zero]))
  refine (hfT.2 ⟨x, hmem⟩).trans ?_
  congr 1
  rw [hLv.chr x hmem hx (Units.mk0 _ hdet) rfl]
  have hsd : Valued.v (NG.supDiag s D.R.r G) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun a _ => Valuation.map_sum_lt _ one_ne_zero fun b _ => ?_
    split_ifs with hab
    · exact hcol a b hab.2 (fun e => by rw [e] at hab; omega)
    · simp
  rw [hψ.1 _ hsd, one_mul, comp_agree _ s _ ξ _ c hc hci hξ (hS.mu i s.w hw j hj)]
  exact (GlobalTheory.BlockType.blockChar_eq _ _ _ hcdet).symm
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.V0TLeISupEigenspaceStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_space_le_iSup_eigenspace_of_goodness : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host), HkCond D T i j k P →
      V0T D T S In.rho In.chi In.θ i j b ≤
        ⨆ σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ},
          Module.End.eigenspace (hkT D T S In i j b k P)
            (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)) := by
  first | exact @_root_.GlobalTheory.HeightCounting.FormsStep.v0t_le_supr_eigenspace | exact _root_.GlobalTheory.HeightCounting.FormsStep.v0t_le_supr_eigenspace | (intros; apply _root_.GlobalTheory.HeightCounting.FormsStep.v0t_le_supr_eigenspace <;> assumption)
end
end

