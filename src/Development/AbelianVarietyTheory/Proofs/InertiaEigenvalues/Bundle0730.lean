import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0447
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0443
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0668
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0954
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0722
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0723
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0677
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsProductsCosocles

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenConductor
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

namespace GlobalTheory.ExtTheta

variable {D : D7}

theorem isoTyp_congr {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) {S S' : Submodule ℂ (GAf L n → W)}
    (hS : ∀ h, ∀ f ∈ S, NG.rt L n h f ∈ S) (h : NG.IsoRep S S') : NG.isoTyp ρ S = NG.isoTyp ρ S' := by
  unfold NG.isoTyp
  congr 1
  ext T
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (h.symm hS).trans h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h.trans h2⟩⟩

theorem transport (U : AUSide D) (M : MtFam D) {μ₀ μ₁ : D.what₂.Tup} {j₀ j₁ : ℕ} (hμ : μ₀ = μ₁) (hj : j₀ = j₁)
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

variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E}

theorem splitOut_of {big₀ big₁ : D.what₂.places.Pl → Finset ℂ} {X₀ X₁ : LocNd (lay0 D)} {T₀ : LocTw X₀} {T₁ : LocTw X₁}
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

theorem muC_eq {X₀ X₁ : LocNd (lay0 D)} {iq₀ : ∀ i : X₀.nd.Loc, FractionRing (X₀.nd.O i) →+* Qbar (X₀.nd.l i)}
    {iq₁ : ∀ i : X₁.nd.Loc, FractionRing (X₁.nd.O i) →+* Qbar (X₁.nd.l i)} {Y₀ : LocAut X₀} {Y₁ : LocAut X₁}
    {C₀ : LocBC Y₀} {C₁ : LocBC Y₁} (U₀ : AutSpec A M tup iq₀ Y₀ C₀) (U₁ : AutSpec A M tup iq₁ Y₁ C₁)
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

theorem zn_of {X₀ X₁ : LocNd (lay0 D)} {iq₀ : ∀ i : X₀.nd.Loc, FractionRing (X₀.nd.O i) →+* Qbar (X₀.nd.l i)}
    {iq₁ : ∀ i : X₁.nd.Loc, FractionRing (X₁.nd.O i) →+* Qbar (X₁.nd.l i)} {Y₀ : LocAut X₀} {Y₁ : LocAut X₁}
    {C₀ : LocBC Y₀} {C₁ : LocBC Y₁} (U₀ : AutSpec A M tup iq₀ Y₀ C₀) (U₁ : AutSpec A M tup iq₁ Y₁ C₁)
    (i₀ : X₀.nd.Loc) (i₁ : X₁.nd.Loc) (hw : X₀.nd.w i₀ = X₁.nd.w i₁) (hj : X₀.nd.j i₀ = X₁.nd.j i₁)
    (hs : ∀ v, SplitOut X₀.nd i₀ v → SplitOut X₁.nd i₁ v) (x₀ : X₀.nd.X i₀) (x₁ : X₁.nd.X i₁)
    (he : ∀ v k, SplitOut X₀.nd i₀ v → 1 ≤ k → k ≤ D.R.nV →
      iotaO X₁.nd Y₁.naut i₁ ((X₁.nd.hT i₁ v k : X₁.nd.X i₁ → X₁.nd.O i₁) x₁) =
        iotaO X₀.nd Y₀.naut i₀ ((X₀.nd.hT i₀ v k : X₀.nd.X i₀ → X₀.nd.O i₀) x₀))
    (h : x₁ ∈ ZN X₁.nd Y₁.naut i₁) : x₀ ∈ ZN X₀.nd Y₀.naut i₀ := by
  have hμ : X₀.nd.mu i₀ = X₁.nd.mu i₁ := by rw [X₀.nd.mu_w, X₁.nd.mu_w, hw]
  have hm := muC_eq U₀ U₁ i₀ i₁ hμ hj
  obtain ⟨P₁, hP₁, Pa, ⟨c1, c2, c3, c4, c5, c6⟩, hmem⟩ := h
  have ne := Y₁.naut.typeV_ne i₁ P₁
  rw [U₁.typeV] at ne
  obtain ⟨P₀, t1, t2, t3, t4⟩ := transport A.au M hμ hj (X₀.nd.j_range i₀).1 (X₀.nd.j_range i₀).2 (X₁.nd.j_range i₁).1
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

theorem theta_loci : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ big₁ : D.what₂.places.Pl → Finset ℂ) (L₀ L₁ : LocAll (lay0 D)), Built A M C tp.tup big₀ L₀ → Built A M C tp.tup big₁ L₁ → ∀ (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc), L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ → L₀.lay.fixZ.nd.j i₀ = L₁.lay.fixZ.nd.j i₁ → ∀ e : L₁.lay.fixZ.nd.X i₁ ≃ L₀.lay.fixZ.nd.X i₀, (∀ (v : PlE D.host) (k : ℕ) (x : L₁.lay.fixZ.nd.X i₁), SplitOut L₁.lay.fixZ.nd i₁ v → 1 ≤ k → k ≤ D.R.nV → iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ ((L₁.lay.fixZ.nd.hT i₁ v k : L₁.lay.fixZ.nd.X i₁ → L₁.lay.fixZ.nd.O i₁) x) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ ((L₀.lay.fixZ.nd.hT i₀ v k : L₀.lay.fixZ.nd.X i₀ → L₀.lay.fixZ.nd.O i₀) (e x))) → ∀ x, x ∈ L₁.lay.fixZ.nd.Z i₁ ↔ e x ∈ L₀.lay.fixZ.nd.Z i₀ := by
  intro _ D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ _ _ _ big₀ big₁ L₀ L₁ ⟨Sp₀, ⟨U₀⟩, _⟩ ⟨Sp₁, ⟨U₁⟩, _⟩ i₀ i₁ hw hj e he x
  have s01 := splitOut_of Sp₀ Sp₁ i₀ i₁ hw
  have s10 := splitOut_of Sp₁ Sp₀ i₁ i₀ hw.symm
  refine (L₁.lay.zOk_fixZ.1 i₁ x).trans (Iff.trans ⟨fun h => ?_, fun h => ?_⟩ (L₀.lay.zOk_fixZ.1 i₀ (e x)).symm)
  · exact zn_of U₀ U₁ i₀ i₁ hw hj s01 (e x) x (fun v k h1 h2 h3 => he v k x (s01 v h1) h2 h3) h
  · exact zn_of U₁ U₀ i₁ i₀ hw.symm hj.symm s10 x (e x) (fun v k h1 h2 h3 => (he v k x h1 h2 h3).symm) h

end GlobalTheory.ExtTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.CoefDuty.ExtRing

theorem qCast_trans {a p q : ℕ} [Fact a.Prime] [Fact p.Prime] [Fact q.Prime] (ι : Qbar a ≃+* ℂ) (h₀ : a = p)
    (h₁ : a = q) (hl : p = q) : qCast h₁ ι = qCast hl (qCast h₀ ι) := by
  subst h₀; subst hl; rfl

theorem exists_gens {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : FractionRing O →+* Qbar l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    ∃ s : Finset (Qbar l), ∀ x, ι x ∈ Submodule.span ℚ_[l] (s : Set (Qbar l)) := by
  classical
  obtain ⟨K, hK, hfd, -⟩ := GlobalTheory.Proof.CoefField.exists_coefField ι hι
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℚ_[l] K).FG)
  refine ⟨t.image Subtype.val, fun x => ?_⟩
  have hx : (⟨ι x, (hK _).2 ⟨x, rfl⟩⟩ : K) ∈ Submodule.span ℚ_[l] (t : Set K) := ht ▸ Submodule.mem_top
  have := Submodule.mem_map_of_mem (f := K.val.toLinearMap) hx
  rw [← Submodule.span_image] at this
  rw [Finset.coe_image]
  exact this

theorem exists_ringHom {l₀ l₁ : ℕ} [Fact l₀.Prime] [Fact l₁.Prime] (hl : l₀ = l₁)
    {O₀ : Type} [cr₀ : CommRing O₀] [dm₀ : IsDomain O₀] [dv₀ : IsDiscreteValuationRing O₀] [al₀ : Algebra ℤ_[l₀] O₀]
    [fi₀ : Module.Finite ℤ_[l₀] O₀]
    {O₁ : Type} [cr₁ : CommRing O₁] [dm₁ : IsDomain O₁] [dv₁ : IsDiscreteValuationRing O₁] [al₁ : Algebra ℤ_[l₁] O₁]
    [fi₁ : Module.Finite ℤ_[l₁] O₁]
    (ι₀ : FractionRing O₀ →+* Qbar l₀)
    (hι₀ : ∀ z : ℤ_[l₀], ι₀ (algebraMap O₀ (FractionRing O₀) (algebraMap ℤ_[l₀] O₀ z)) =
      algebraMap ℚ_[l₀] (Qbar l₀) (z : ℚ_[l₀]))
    (ι₁ : FractionRing O₁ →+* Qbar l₁)
    (hι₁ : ∀ z : ℤ_[l₁], ι₁ (algebraMap O₁ (FractionRing O₁) (algebraMap ℤ_[l₁] O₁ z)) =
      algebraMap ℚ_[l₁] (Qbar l₁) (z : ℚ_[l₁]))
    (c₀ : Qbar l₀ ≃+* ℂ) (c₁ : Qbar l₁ ≃+* ℂ) (hc : c₁ = qCast hl c₀) (s : Set (Qbar l₀))
    (hs : ∀ x, ι₀ x ∈ Submodule.span ℚ_[l₀] s) (hs₁ : ∀ y ∈ s, ∃ x, c₁ (ι₁ x) = c₀ y) :
    ∃ φ : O₀ →+* O₁, (∀ z, c₁ (ι₁ (algebraMap O₁ _ (φ z))) = c₀ (ι₀ (algebraMap O₀ _ z))) ∧
      ∀ (z : ℤ_[l₀]) (z' : ℤ_[l₁]), HEq z z' → φ (algebraMap ℤ_[l₀] O₀ z) = algebraMap ℤ_[l₁] O₁ z' := by
  subst hl
  have hc' : ∀ x, c₁ x = c₀ x := fun x => by rw [hc]; rfl
  simp only [hc'] at hs₁ ⊢
  obtain ⟨K₀, hK₀, -, hn₀⟩ := GlobalTheory.Proof.CoefField.exists_coefField ι₀ hι₀
  obtain ⟨K₁, hK₁, -, hn₁⟩ := GlobalTheory.Proof.CoefField.exists_coefField ι₁ hι₁
  have hsK : s ⊆ (K₁ : Set (Qbar l₀)) := by
    intro y hy
    obtain ⟨x, hx⟩ := hs₁ y hy
    exact (hK₁ y).2 ⟨x, c₀.injective hx⟩
  have hspan : Submodule.span ℚ_[l₀] s ≤ K₁.toSubalgebra.toSubmodule := Submodule.span_le.2 hsK
  let f₀ : O₀ →+* Qbar l₀ := ι₀.comp (algebraMap O₀ (FractionRing O₀))
  let f₁ : O₁ →+* Qbar l₀ := ι₁.comp (algebraMap O₁ (FractionRing O₁))
  have hf₁ : Function.Injective f₁ := ι₁.injective.comp (IsFractionRing.injective O₁ (FractionRing O₁))
  have hrange : ∀ z, f₀ z ∈ f₁.range := by
    intro z
    have h1 : f₀ z ∈ K₁ := hspan (hs _)
    obtain ⟨y, hy⟩ := (hK₁ _).1 h1
    have hle : ‖ι₀ (algebraMap O₀ (FractionRing O₀) z)‖ ≤ 1 := (hn₀ _).2 ⟨z, rfl⟩
    have hy1 : ‖ι₁ y‖ ≤ 1 := by rw [hy]; exact hle
    obtain ⟨u, rfl⟩ := (hn₁ y).1 hy1
    exact ⟨u, hy⟩
  let e₁ : O₁ ≃+* f₁.range := RingEquiv.ofBijective f₁.rangeRestrict
    ⟨fun a b h => hf₁ (congrArg Subtype.val h), f₁.rangeRestrict_surjective⟩
  let φ : O₀ →+* O₁ := e₁.symm.toRingHom.comp (f₀.codRestrict f₁.range hrange)
  have hφ : ∀ z, f₁ (φ z) = f₀ z := by
    intro z
    have : e₁ (φ z) = f₀.codRestrict f₁.range hrange z := e₁.apply_symm_apply _
    exact congrArg Subtype.val this
  refine ⟨φ, fun z => congrArg c₀ (hφ z), fun z z' hzz => ?_⟩
  cases eq_of_heq hzz
  apply hf₁
  rw [hφ]
  change ι₀ _ = ι₁ _
  rw [hι₀, hι₁]

end GlobalTheory.CoefDuty.ExtRing

end

open GlobalTheory.CoefDuty.ExtRing in
set_option maxHeartbeats 2000000 in

theorem GlobalTheory.CoefDuty.ExtRing.ext_ring : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ : D.what₂.places.Pl → Finset ℂ) (L₀ : LocAll (lay0 D)), Built A M C tp.tup big₀ L₀ → ∃ big₁ : D.what₂.places.Pl → Finset ℂ, ∀ L₁ : LocAll (lay0 D), Built A M C tp.tup big₁ L₁ → ∀ (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc), L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ → ∃ φ : L₀.lay.fixZ.nd.O i₀ →+* L₁.lay.fixZ.nd.O i₁, (∀ z, iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ (φ z) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ z) ∧ ∀ (z : ℤ_[L₀.lay.fixZ.nd.l i₀]) (z' : ℤ_[L₁.lay.fixZ.nd.l i₁]), HEq z z' → φ (algebraMap _ _ z) = algebraMap _ _ z' := by
  classical
  intro _ D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ _ _ _ big₀ L₀ hB₀
  obtain ⟨Sp₀, ⟨Au₀⟩, -⟩ := hB₀
  have hg := fun i => exists_gens (Sp₀.iq i) (Sp₀.iq_alg i)
  let gens : ∀ i : L₀.X.nd.Loc, Finset (Qbar (L₀.X.nd.l i)) := fun i => Classical.choose (hg i)
  have hgens : ∀ i x, Sp₀.iq i x ∈ Submodule.span ℚ_[L₀.X.nd.l i] (gens i : Set (Qbar (L₀.X.nd.l i))) :=
    fun i => Classical.choose_spec (hg i)
  let big₁ : D.what₂.places.Pl → Finset ℂ := fun w => (Finset.Icc 1 D.R.m).biUnion fun j =>
    (L₀.X.nd.locs j w).biUnion fun i => (gens i).image fun y => qCast (L₀.X.nd.w_l i) (A.pl.ι (L₀.X.nd.w i)) y
  have hbig : ∀ i y, y ∈ gens i → qCast (L₀.X.nd.w_l i) (A.pl.ι (L₀.X.nd.w i)) y ∈ big₁ (L₀.X.nd.w i) := by
    intro i y hy
    refine Finset.mem_biUnion.2 ⟨L₀.X.nd.j i, Finset.mem_Icc.2 (L₀.X.nd.j_range i), ?_⟩
    exact Finset.mem_biUnion.2 ⟨i, (L₀.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩, Finset.mem_image_of_mem _ hy⟩
  refine ⟨big₁, fun L₁ hB₁ i₀ i₁ hw => ?_⟩
  obtain ⟨Sp₁, ⟨Au₁⟩, -⟩ := hB₁
  change L₀.X.nd.w i₀ = L₁.X.nd.w i₁ at hw
  have hl : L₀.X.nd.l i₀ = L₁.X.nd.l i₁ := by
    exact (L₀.X.nd.w_l i₀).symm.trans ((congrArg _ hw).trans (L₁.X.nd.w_l i₁))
  haveI := L₀.X.nd.lPrime i₀
  haveI := L₁.X.nd.lPrime i₁
  have key : ∀ w (_ : L₀.X.nd.w i₀ = w) (h₁ : D.what₂.places.resChar w = L₁.X.nd.l i₁),
      qCast h₁ (A.pl.ι w) = qCast hl (qCast (L₀.X.nd.w_l i₀) (A.pl.ι (L₀.X.nd.w i₀))) := by
    intro w hw' h₁
    subst hw'
    exact qCast_trans _ _ _ _
  obtain ⟨φ, h1, h2⟩ := exists_ringHom (O₀ := L₀.X.nd.O i₀) (O₁ := L₁.X.nd.O i₁)
    (cr₀ := L₀.X.nd.instO i₀) (dm₀ := L₀.X.nd.domO i₀) (dv₀ := L₀.X.nd.dvrO i₀) (al₀ := L₀.X.nd.algO i₀) (fi₀ := L₀.X.nd.finO i₀)
    (cr₁ := L₁.X.nd.instO i₁) (dm₁ := L₁.X.nd.domO i₁) (dv₁ := L₁.X.nd.dvrO i₁) (al₁ := L₁.X.nd.algO i₁) (fi₁ := L₁.X.nd.finO i₁) hl (Sp₀.iq i₀) (Sp₀.iq_alg i₀) (Sp₁.iq i₁) (Sp₁.iq_alg i₁)
    (qCast (L₀.X.nd.w_l i₀) (A.pl.ι (L₀.X.nd.w i₀))) (qCast (L₁.X.nd.w_l i₁) (A.pl.ι (L₁.X.nd.w i₁)))
    (key _ hw _) _ (hgens i₀) (fun y hy => Sp₁.iq_big i₁ _ (hw ▸ hbig i₀ y hy))
  refine ⟨φ, fun z => ?_, h2⟩
  have e₀ := fun x => (congrArg (fun g : Qbar (L₀.X.nd.l i₀) ≃+* ℂ => g (L₀.Y.naut.iotaQ i₀ x)) (Au₀.iotaQC i₀)).trans
    (congrArg (qCast (L₀.X.nd.w_l i₀) (A.pl.ι (L₀.X.nd.w i₀))) (DFunLike.congr_fun (Au₀.iotaQ i₀) x))
  have e₁ := fun x => (congrArg (fun g : Qbar (L₁.X.nd.l i₁) ≃+* ℂ => g (L₁.Y.naut.iotaQ i₁ x)) (Au₁.iotaQC i₁)).trans
    (congrArg (qCast (L₁.X.nd.w_l i₁) (A.pl.ι (L₁.X.nd.w i₁))) (DFunLike.congr_fun (Au₁.iotaQ i₁) x))
  exact (e₁ _).trans ((h1 z).trans (e₀ _).symm)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenUnitary
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.EigPlace

theorem finite_and_mem (hstd : HeckeStdPlain) {D : D7} {M : MtFam D} (HT : HeckeTied D M) (av : AVTied D M)
    (T : NormalizedLocalCompatibility D M) (i : D.nd.Loc) (x : D.nd.X i) (Q : Finset (PlE D.host)) (hQ : D.nd.Q i = Q) :
    (EigSet (M (D.what₂.muTw (D.nd.w i)) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2)
        (D.what₂.places.resChar (D.nd.w i)) Q).Finite ∧
      ptSys D i x ∈ EigSet (M (D.what₂.muTw (D.nd.w i)) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2)
        (D.what₂.places.resChar (D.nd.w i)) Q := by
  subst hQ
  have hi : i ∈ D.nd.locs (D.nd.j i) (D.nd.w i) := (D.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  refine ⟨?_, ?_⟩
  · refine GlobalTheory.EigFinite.eigSet_finite hstd D _ _ _ _ _ (badPl D i) ?_ ?_
    · exact hypOutside_transport (D.nd.mu_w i) rfl (D.nd.j_range i).1 (D.nd.j_range i).2 _ _ _ (HT.J_hyp i)
    · intro v k s hg hc
      rw [T.Q_eq _ _ i hi] at hg
      exact genOutBad_of T _ _ i hi v k s hg hc
  · rw [D.nd.w_l i]
    exact GlobalTheory.FitHecke.mt_transport M (fun μ j m => ptSys D i x ∈ EigSet m (D.nd.l i) (D.nd.Q i)) (D.nd.mu_w i) rfl
      (D.nd.j_range i).1 (D.nd.j_range i).2 _ _ (GlobalTheory.PointEigen.ptSys_mem_eigSet D M av i x)

set_option maxHeartbeats 1000000 in

theorem built_finite_and_mem : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd →
    ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tp.tup big L →
    ∀ (i : L.X.nd.Loc) (x : L.X.nd.X i),
      (EigSet (M (D.what₂.muTw (L.X.nd.w i)) (L.X.nd.j i) (L.X.nd.j_range i).1 (L.X.nd.j_range i).2)
        (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i))).Finite ∧
      ptSys (withLoc L) i x ∈ EigSet (M (D.what₂.muTw (L.X.nd.w i)) (L.X.nd.j i) (L.X.nd.j_range i).1 (L.X.nd.j_range i).2)
        (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i)) := by
  intro hstd D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L hB i x
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hB
  obtain ⟨Hk, -⟩ := GlobalTheory.FitHecke.heckeOpen_withLoc D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb
    big L Sp Au
  have hQ : L.X.nd.Q i = C.Q (L.X.nd.w i) :=
    (Sp.Q_eq _ _ i ((L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)
  exact finite_and_mem hstd (D := withLoc L) Hk.hecke Hk.av Hk.cover i x (C.Q (L.X.nd.w i)) hQ

end GlobalTheory.EigPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.Published GlobalTheory.LFun

namespace GlobalTheory.SpehPair

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N a d : ℕ}

theorem isUnitary_of_isNormalised {π : CuspSub E a} (h : IsNormalised π) : π.IsUnitary := by
  obtain ⟨ω, hω⟩ := Central.exists_hasCentral E a π
  have hs : ∀ (b : ℕ) (t : ℝ), splitCentre E b t =
      Matrix.GeneralLinearGroup.scalar (Fin b) (infId E (expU fun _ => (t : ℂ))) := fun b t =>
    (cornerGL_scalar (sInf E) _)
  have h1 : ∀ t : ℝ, ((ω.1 (infId E (expU fun _ => (t : ℂ))) : ℂˣ) : ℂ) = 1 := fun t => by
    obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
    obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h0 (Subtype.ext (funext hc))
    have h2 := hω.apply hφ (infId E (expU fun _ => (t : ℂ))) g
    rw [← hs, h φ hφ] at h2
    exact mul_right_cancel₀ hg (h2.symm.trans (one_mul _).symm)
  have h3 : ((CuspSub.triv E (le_refl 1)).twist ω).HasCentral ω :=
    CuspSub.hasCentral_iff.2 (CG.hasCentChar_ofChar ω)
  have h4 : IsNormalised ((CuspSub.triv E (le_refl 1)).twist ω) := fun φ hφ t g => by
    rw [hs, h3.apply hφ, h1, one_mul]
  exact hω.isUnitary_iff.2 (h3.isUnitary_iff.1 (Model.isUnitary_of_isNormalised h4))

theorem eventually_spherical {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ σ, IsLocCompGL V w σ →
      GlobalTheory.LGrp.IsSpherical σ.ρ (KGL w N) := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  filter_upwards [LocSph.eventually_mem ((hV.aut φ hφ).level.mem_nhds (by simp))] with w hw σ hσ
  obtain ⟨f, hf0, hfV, hf⟩ := hσ
  let F : σ.V →ₗ[ℂ] V := f.codRestrict V hfV
  have hF : ∀ g v, F (σ.ρ g v) = DiscLocEx.locRepD hV.stable w g (F v) := fun g v => Subtype.ext (hf g v)
  have hF0 : F ≠ 0 := fun e => hf0 (LinearMap.ext fun v => congrArg Subtype.val (LinearMap.congr_fun e v))
  have hi : LinearMap.ker F = ⊥ := ((isIrreducible_iff σ.ρ).1 σ.irred).2 _ (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hF, hv, map_zero]) |>.resolve_right fun e => hF0 (LinearMap.ker_eq_top.1 e)
  have hfix : (⟨φ, hφ⟩ : V) ∈ GlobalTheory.PRep.fixed (DiscLocEx.locRepD hV.stable w) (KGL w N) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (by
      obtain ⟨g, rfl⟩ := hk
      exact hw g)
  have h1 : LinearMap.range F ⊓ GlobalTheory.PRep.fixed (DiscLocEx.locRepD hV.stable w) (KGL w N) ≠ ⊥ := fun e =>
    hF0 (LinearMap.range_eq_bot.1 (DiscLocEx.eq_bot_of_fixedD hV w GlobalTheory.SatInd.isCompact_KGL
      (fun e => h0 (congrArg Subtype.val e)) hfix _ (by rintro g _ ⟨v, rfl⟩; exact ⟨_, hF g v⟩) e))
  obtain ⟨_, ⟨⟨v, rfl⟩, hv⟩, hv0⟩ := (Submodule.ne_bot_iff _).1 h1
  exact (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 fun k hk => LinearMap.ker_eq_bot.1 hi (by
    rw [hF, GlobalTheory.LGrp.mem_fixed.1 hv k hk]), fun e => hv0 (by rw [e, map_zero])⟩

theorem exists_sat_twist (hd : 1 ≤ d) {π : CuspSub E a} {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} {σ' : SmIrr (GL (Fin N) (w.adicCompletion E))}
    (hσ : π.IsLocComp w σ) (h : GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ)
    {T : Multiset ℂˣ} (hT : HasSatGL w σ'.ρ T) (ν : ℝ → HChar E) (hν : ∀ s, (ν s).IsAbsPow s) :
    ∃ B : Fin d → Multiset ℂˣ, (∀ i, ((CG.mk π).twist (ν (-spehExp d i))).HasSat w (B i)) ∧ ∑ i, B i = T := by
  obtain ⟨S, hS, e⟩ := GlobalTheory.SatInd.exists_sat_of_isSpeh hd σ.smooth σ.irred h hT
  refine ⟨_, fun i => GlobalTheory.SphGal.hasSatGL_twist E a π _ w S ((hν _).1 w)
    (GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hσ hS), ?_⟩
  refine Multiset.map_injective Units.val_injective (Eq.trans ?_ e)
  refine (map_sum (Multiset.mapAddMonoidHom _) _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
  rw [Multiset.coe_mapAddMonoidHom, Multiset.map_map]
  refine Multiset.map_congr rfl fun z _ => ?_
  simp only [Function.comp_apply, Units.val_mul, (hν _).2.1 w, spehExp]
  congr 2
  push_cast
  ring

end GlobalTheory.SpehPair

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaCoefficientIsSchwartzBruhatUniformSplitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCoefficient_isSchwartzBruhat_uniform_split : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∃ k : ℕ, 0 < k ∧ (∀ u ∈ latH S T ΛS ΛT, IsHalf a u ∨ IsHalf (cA D a) u → heisO ψ S T (k • u) f = f) ∧ ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) ≠ 0 → k • x ∈ latH S T ΛS ΛT) ∧ (∀ ℓ, InvForm ψ S T a ℓ → IsSBHalf a (latH S T ΛS ΛT) (coef ψ S T a ℓ f)) ∧ ∃ X : Finset (WO S T), (∀ x ∈ X, IsHalf a x) ∧ ∀ x, IsHalf a x → (∀ ℓ, InvForm ψ S T a ℓ → ℓ (heisO ψ S T x f) = 0) ∨ ∃ x₁ ∈ X, heisO ψ S T x f = heisO ψ S T x₁ f := by
  first | exact @GlobalTheory.DownLift.SplitCoef.coef_isSBHalf_uniform | exact GlobalTheory.DownLift.SplitCoef.coef_isSBHalf_uniform | (intros; apply GlobalTheory.DownLift.SplitCoef.coef_isSBHalf_uniform <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLevelTypeMemSpanAveragesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_levelType_mem_span_averages : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeVec R i t f → f ∈ Submodule.span ℂ ({φ | GlobalTheory.DownLift.GenFinite.TypeVec R i t φ ∧ GlobalTheory.DownLift.GenFinite.Clean R i t φ} ∪ GlobalTheory.DownLift.GenFinite.AvgIm R i t) := by
  first | exact @GlobalTheory.DownLift.GenFinite.cleanSpan | exact GlobalTheory.DownLift.GenFinite.cleanSpan | (intros; apply GlobalTheory.DownLift.GenFinite.cleanSpan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVectorSchroedingerImageAtLevelPrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftVector_schroedingerImage_at_levelPrime : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (P : Pl D.host.E), P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ k, SuppF (Wc D i) f k → ∃ (ea : AE D) (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)) (c : ℂ), IsIdemSum ea (R.Pg ∪ R.Q t) ∧ IsSplitIdem D e ∧ e * ea = e ∧ f = e + cA D e ∧ IsStdChar D R.ψ (-1) ∧ IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsSelfDualC (Wc D i) (R.ΛW i) ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) ∧ IsLatVac (heisO R.ψ (Vc D i) (Wc D i)) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (R.vacP i) ∧ IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) 1 (R.vacP i) Tm ∧ IsSBHalf (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (datP R i t ea) ∧ IsSBHalf (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (fun x => datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x)) ∧ R.vP i t = Tm (datP R i t ea) ∧ R.ωP i t (1, k) (R.vP i t) = c • Tm (fun x => datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x)) := by
  first | exact @GlobalTheory.BadPlace.vec_read_at | exact GlobalTheory.BadPlace.vec_read_at | (intros; apply GlobalTheory.BadPlace.vec_read_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsCuspidalTwistsCharactersStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_keeps_cuspidal_twists_characters : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → (∀ (x : IrrGL k) (x' : IrrGL k'), RepRel i x x' → (x.IsCusp ↔ x'.IsCusp) ∧ ∀ s : ℂ, RepRel i (x.nu s) (x'.nu s)) ∧ ∀ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (χ' : k'ˣ →* ℂˣ) (hχ' : IsSmoothChar χ'), (∀ x, χ' (Units.map i.toRingHom.toMonoidHom x) = χ x) → RepRel i (IrrGL.ofChar χ hχ) (IrrGL.ofChar χ' hχ') := by
  first | exact @GlobalTheory.LocLanglands.repRel_isCusp_nu_ofChar | exact GlobalTheory.LocLanglands.repRel_isCusp_nu_ofChar | (intros; apply GlobalTheory.LocLanglands.repRel_isCusp_nu_ofChar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsProductsCosoclesStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_keeps_products_cosocles : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (r N : ℕ) (x : Fin r → IrrGL k) (x' : Fin r → IrrGL k') (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x' a).1 = N) (y : IrrRep (GL (Fin N) k)) (y' : IrrRep (GL (Fin N) k')), (∀ a, RepRel i (x a) (x' a)) → RepRel i (cls y) (cls y') → IsCosocle y.ρ (prodIrr x hd) → IsCosocle y'.ρ (prodIrr x' hd') := by
  first | exact @GlobalTheory.FieldTransport.isCosocle_prodIrr_transport | exact GlobalTheory.FieldTransport.isCosocle_prodIrr_transport | (intros; apply GlobalTheory.FieldTransport.isCosocle_prodIrr_transport <;> assumption)
end

