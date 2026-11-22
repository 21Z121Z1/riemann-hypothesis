import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0702
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0794
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0730
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0793
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0803
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0737
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0804
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsLocExtFinrankEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0099
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransport
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.FieldCompat

section Rep

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem repRel_symm {i : k ≃+* k'} {x : IrrGL k} {x' : IrrGL k'} (H : RepRel i x x') : RepRel i.symm x' x := by
  obtain ⟨n, π, π', e, rfl, rfl, he⟩ := H
  refine ⟨n, π', π, e.symm, rfl, rfl, fun g v => ?_⟩
  obtain ⟨v, rfl⟩ := e.surjective v
  have hg : GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom g) = g := by
    ext a b
    simp [GeneralLinearGroup.map]
  rw [LinearEquiv.symm_apply_eq, e.symm_apply_apply, he, hg]

theorem cls_rep (x : IrrGL k) : cls x.2.rep = x := congrArg (Sigma.mk x.1) x.2.cl_rep

theorem exists_cls {x : IrrGL k} {n : ℕ} (hn : x.1 = n) : ∃ π : IrrRep (GL (Fin n) k), cls π = x := by
  subst hn
  exact ⟨x.2.rep, cls_rep x⟩

theorem isCusp_cls {n : ℕ} (π : IrrRep (GL (Fin n) k)) : (cls π).IsCusp ↔ 0 < n ∧ IsCuspidal π.ρ :=
  IrrGL.isCusp_of (π := π.ρ) (hs := π.smooth) (hi := π.irr)

theorem isSmoothChar_comp (i : k' ≃+* k) (hi : Continuous i) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    IsSmoothChar (χ.comp (Units.map i.toRingHom.toMonoidHom)) := by
  have hc : Continuous (Units.map i.toRingHom.toMonoidHom : k'ˣ → kˣ) := Continuous.units_map _ hi
  exact IsOpen.preimage hc hχ

end Rep

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}

theorem charZero_compl (w : HeightOneSpectrum (𝓞 E)) : CharZero (w.adicCompletion E) :=
  charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective

def psiMap (i : w.adicCompletion E ≃+* w'.adicCompletion E') (ψ : AddChar (w.adicCompletion E) Circle) :
    AddChar (w'.adicCompletion E') Circle := ψ.compAddMonoidHom i.symm.toAddMonoidHom

theorem psiMap_apply (i : w.adicCompletion E ≃+* w'.adicCompletion E') (ψ : AddChar (w.adicCompletion E) Circle)
    (y : w'.adicCompletion E') : psiMap i ψ y = ψ (i.symm y) := rfl

theorem exists_of_wdRel {φ : Ω ≃+* Ω'} {y : WD h} {y' : WD h'} (H : WDRel φ y y') {n : ℕ} (hn : y.lpDim = n) :
    ∃ (b : WDRep h (Fin n → ℂ)) (b' : WDRep h' (Fin n → ℂ)), WD.mk b = y ∧ WD.mk b' = y' ∧
      b.N = b'.N ∧ ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, φ ((σ : G E Ω) z) = (σ' : G E' Ω') (φ z)) → b.ρ σ = b'.ρ σ' := by
  obtain ⟨m, b, b', rfl, hb', h1, h2⟩ := H
  obtain rfl : m = n := by simpa using hn
  exact ⟨b, b', rfl, hb', h1, h2⟩

theorem fieldCompatible : GlobalArtinReciprocity → ChevalleyUnits → BrauerDegreeZero → LocalLanglandsExists → LocalConverseGL → LanglandsExhaustionGL → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h'), IsRecLit h rc → IsRecLit h' rc' → FieldCompatible rc rc' := by
  intro hG hC hB hL hLC hLE hBZ E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' rc rc'
    ⟨a, ha, ε, hε, H⟩ ⟨a', ha', ε', hε', H'⟩ φ j i h1 h2 h3 h4 n π π' e he
  have P : PlaceIso A w A' w' φ j i := ⟨h1, h2, h3, h4⟩
  have := charZero_compl w
  have := charZero_compl w'
  have hs : Continuous i.symm := (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation _ _ i h3).1
  obtain ⟨T, hT, hTd⟩ := GlobalTheory.T.transportIrrGL_bijective_degree_charZero _ _ i h3
  obtain ⟨hcu, hch⟩ := GlobalTheory.T.transport_keeps_cuspidal_twists_characters _ _ i h3
  obtain ⟨S, hS, hSd, hS0, hSs, hSc, hSt, hSp, hSi, hSo⟩ := GlobalTheory.T.place_over_transport_ring_iso_symm E Ω A w h E' Ω' A' w' h' φ j i P
  have hart := GlobalTheory.T.localArtinMap_unique_transport_placeIso hG hC E Ω A w h E' Ω' A' w' h' φ j i P a a' ha ha'
  have hrel : ∀ x, RepRel i x (T x) := fun x => (hT _ _).2 rfl
  have hcusp : ∀ x, x.IsCusp ↔ (T x).IsCusp := fun x => (hcu _ _ (hrel x)).1
  have hpsi : ∀ ψ : AddChar (w.adicCompletion E) Circle, ∀ x, psiMap i ψ (i x) = ψ x := fun ψ x => by
    rw [psiMap_apply, RingEquiv.symm_apply_apply]
  have M : LawsMin a ha (fun ψ y => ε' E' w' h' (psiMap i ψ) (S y)) (fun x => S.symm (rc' (T x))) := by
    refine ⟨S.symm.bijective.comp (H'.bij.comp T.bijective), fun x => ?_, fun χ hχ => ?_, fun ψ hψ hψ1 m ρ τ hρ => ?_,
      fun x => ?_, fun l x hx => ?_⟩
    · rw [← hSd, S.apply_symm_apply, H'.dim, hTd]
    · have hχ' := isSmoothChar_comp i.symm hs hχ
      have hv : ∀ x, (χ.comp (Units.map i.symm.toRingHom.toMonoidHom)) (Units.map i.toRingHom.toMonoidHom x) = χ x :=
        fun x => congrArg χ (Units.ext (by simp))
      rw [(hT _ _).1 (hch χ hχ _ hχ' hv), H'.one, Equiv.symm_apply_eq]
      refine (hSo _ _ _ _ fun σ σ' hσ => ?_).symm
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply _ a', hart σ σ' hσ, hv]
    · obtain ⟨ρ', hρ'⟩ := exists_cls (hTd (cls ρ))
      obtain ⟨τ', hτ'⟩ := exists_cls (hTd (cls τ))
      have hc : IsCuspidal ρ'.ρ :=
        ((isCusp_cls ρ').1 (hρ' ▸ (hcusp _).1 ((isCusp_cls ρ).2 ⟨Nat.succ_pos m, hρ⟩))).2
      have hne : psiMap i ψ ≠ 1 := fun h0 => hψ1 (AddChar.ext _ _ fun x => by rw [← hpsi, h0]; rfl)
      have key := H'.eps (psiMap i ψ) (hψ.comp hs) hne m ρ' τ' hc
      rw [hρ', hτ'] at key
      simp only [hSc, S.apply_symm_apply]
      exact GlobalTheory.T.rankin_selberg_epsilon_transport _ _ i.symm hs (psiMap i ψ) ψ (fun _ => rfl) m ρ' ρ τ' τ _
        (repRel_symm (hρ' ▸ hrel _)) (repRel_symm (hτ' ▸ hrel _)) key
    · rw [hcusp, H'.cusp, ← hSi, S.apply_symm_apply]
    · let f : Segment (w.adicCompletion E) → Segment (w'.adicCompletion E') := fun Δ =>
        Segment.ofFirst (T Δ.first) ((hcusp _).1 Δ.isCusp_first) Δ.len Δ.len_pos
      have hl := GlobalTheory.T.isLanglandsData_transport_localFieldIso _ _ i h3 l (l.map f) x (T x)
        (by rw [List.forall₂_map_right_iff, List.forall₂_same]; exact fun Δ _ => ⟨hrel _, rfl⟩) (hrel x) hx
      rw [H'.langlands _ _ hl, Equiv.symm_apply_eq]
      clear hl hx
      induction l with
      | nil => exact hS0.symm
      | cons Δ l ih =>
        simp only [segSum, sumList, List.map_cons, List.foldr_cons] at ih ⊢
        rw [hSs, ← ih, hSc, hSt, hSp, S.apply_symm_apply]
        rfl
  obtain ⟨ψ, hψ, hψ1⟩ := exists_continuous_addChar_ne_one (w.adicCompletion E)
  have hE : ε E w h ψ = fun y => ε' E' w' h' (psiMap i ψ) (S y) := funext fun y =>
    GlobalTheory.T.rec_transport_field_iso hG hC hB hL E Ω A w h E' Ω' A' w' h' φ j i P ε ε' hε hε' ψ _ hψ hψ1 (hpsi ψ) y _ ((hS _ _).2 rfl)
  have hrc := GlobalTheory.T.rec_unique_of_laws hLC hLE hBZ E Ω A w h a ha _ rc _ ψ _ hψ hψ1 hE H.toLawsMin M
  have hπ : T (cls π) = cls π' := (hT _ _).1 ⟨n, π, π', e, rfl, rfl, he⟩
  refine exists_of_wdRel ((hS _ _).2 ?_) (H.dim _)
  rw [congrFun hrc (cls π), S.apply_symm_apply, hπ]

end GlobalTheory.LocLanglands.FieldCompat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenWeight
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.PtExt

set_option maxHeartbeats 1000000 in

theorem main : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ big₁ : D.what₂.places.Pl → Finset ℂ) (L₀ L₁ : LocAll (lay0 D)), Built A M C tp.tup big₀ L₀ → Built A M C tp.tup big₁ L₁ → ∀ i₁ : L₁.lay.fixZ.nd.Loc, ∃ i₀ : L₀.lay.fixZ.nd.Loc, L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ ∧ L₀.lay.fixZ.nd.j i₀ = L₁.lay.fixZ.nd.j i₁ ∧ ∃ e : L₁.lay.fixZ.nd.X i₁ ≃ L₀.lay.fixZ.nd.X i₀, ∀ (v : PlE D.host) (k : ℕ) (x : L₁.lay.fixZ.nd.X i₁), SplitOut L₁.lay.fixZ.nd i₁ v → 1 ≤ k → k ≤ D.R.nV → iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ ((L₁.lay.fixZ.nd.hT i₁ v k : L₁.lay.fixZ.nd.X i₁ → L₁.lay.fixZ.nd.O i₁) x) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ ((L₀.lay.fixZ.nd.hT i₀ v k : L₀.lay.fixZ.nd.X i₀ → L₀.lay.fixZ.nd.O i₀) (e x)) := by
  intro hstd D cf jE A low Pq S hL eig θ Bs M C tp hch hmt hstar hexp hspl hcheb big₀ big₁ L₀ L₁ hB₀ hB₁ i₁
  have onto : ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tp.tup big L →
      ∀ (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 →
      ∀ c ∈ EigSet (M (D.what₂.muTw w) j h1 h2) (D.what₂.places.resChar w) (C.Q w),
        ∃ i ∈ L.X.nd.locs j w, ∃ x : L.X.nd.X i, sys L i x = c := by
    intro big L hB j w h1 h2 htw c hc
    obtain ⟨i, hi, x, hx⟩ := GlobalTheory.T.side_eigen_frobenius hstd D cf jE A low Pq S hL eig θ Bs M C tp hch hmt hstar hexp hspl hcheb big L hB j w h1 h2 htw c hc
    refine ⟨i, hi, x, funext fun v => funext fun k => ?_⟩
    by_cases hg : GenAt D (D.what₂.places.resChar w) (C.Q w) v k
    · rw [sys_of_genAt hB hi x hg, hx v k hg]
    · rw [sys_of_not_genAt hB hi x hg, hc.1 v k hg]
  have cong : ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tp.tup big L →
      ∀ (j : ℕ) (w : D.what₂.places.Pl) (i i' : L.X.nd.Loc), i ∈ L.X.nd.locs j w → i' ∈ L.X.nd.locs j w →
      ∀ (x : L.X.nd.X i) (x' : L.X.nd.X i'),
        (i = i' ↔ ∀ v k, sys L i x v k - sys L i' x' v k ∈ (A.pl.plB w).nonunits) := by
    intro big L hB j w i i' hi hi' x x'
    rw [GlobalTheory.T.locations_distinguished_by_generics D cf jE A M C tp.tup big L hB j w i i' hi hi' x x']
    constructor
    · intro h v k
      by_cases hg : GenAt D (D.what₂.places.resChar w) (C.Q w) v k
      · rw [sys_of_genAt hB hi x hg, sys_of_genAt hB hi' x' hg]; exact h v k hg
      · rw [sys_of_not_genAt hB hi x hg, sys_of_not_genAt hB hi' x' hg, sub_zero]; exact zero_mem _
    · intro h v k hg
      rw [← sys_of_genAt hB hi x hg, ← sys_of_genAt hB hi' x' hg]; exact h v k
  have h1 := (L₁.X.nd.j_range i₁).1
  have h2 := (L₁.X.nd.j_range i₁).2
  have hi₁ : i₁ ∈ L₁.X.nd.locs (L₁.X.nd.j i₁) (L₁.X.nd.w i₁) := (L₁.X.nd.locs_mem _ _ i₁).2 ⟨rfl, rfl⟩
  have htw : D.what₂.muAt (L₁.X.nd.w i₁) ≠ D.what₂.mu0 := L₁.X.nd.w_tw i₁
  obtain ⟨x₁⟩ := L₁.X.nd.neX i₁
  obtain ⟨i₀, hi₀, y₀, hy₀⟩ := onto big₀ L₀ hB₀ _ _ h1 h2 htw _ (sys_mem hB₁ h1 h2 hi₁ x₁)
  have fwd : ∀ x : L₁.X.nd.X i₁, ∃ y : L₀.X.nd.X i₀, sys L₀ i₀ y = sys L₁ i₁ x := by
    intro x
    obtain ⟨i', hi', y', hy'⟩ := onto big₀ L₀ hB₀ _ _ h1 h2 htw _ (sys_mem hB₁ h1 h2 hi₁ x)
    have hc : i' = i₀ := by
      rw [cong big₀ L₀ hB₀ _ _ i' i₀ hi' hi₀ y' y₀, hy', hy₀]
      exact (cong big₁ L₁ hB₁ _ _ i₁ i₁ hi₁ hi₁ x x₁).1 rfl
    subst hc
    exact ⟨y', hy'⟩
  choose f hf using fwd
  have finj : Function.Injective f := fun x x' h => sys_inj L₁ i₁ (by rw [← hf x, ← hf x', h])
  have fsurj : Function.Surjective f := by
    intro y
    obtain ⟨i', hi', x', hx'⟩ := onto big₁ L₁ hB₁ _ _ h1 h2 htw _ (sys_mem hB₀ h1 h2 hi₀ y)
    have hc : i' = i₁ := by
      rw [cong big₁ L₁ hB₁ _ _ i' i₁ hi' hi₁ x' x₁, hx', ← hy₀]
      exact (cong big₀ L₀ hB₀ _ _ i₀ i₀ hi₀ hi₀ y y₀).1 rfl
    subst hc
    exact ⟨x', sys_inj L₀ i₀ (by rw [hf x', hx'])⟩
  have hw₀ : L₀.X.nd.w i₀ = L₁.X.nd.w i₁ := ((L₀.X.nd.locs_mem _ _ i₀).1 hi₀).2
  have hj₀ : L₀.X.nd.j i₀ = L₁.X.nd.j i₁ := ((L₀.X.nd.locs_mem _ _ i₀).1 hi₀).1
  refine ⟨i₀, hw₀, hj₀, Equiv.ofBijective f ⟨finj, fsurj⟩, fun v k x hv k1 k2 => ?_⟩
  have hg := (splitOut_iff_genAt hB₁ hi₁ v k).1 ⟨hv, k1, k2⟩
  have e := congrFun (congrFun (hf x) v) k
  rw [sys_of_genAt hB₀ hi₀ _ hg] at e
  exact (sys_of_genAt hB₁ hi₁ x hg).symm.trans e.symm

end GlobalTheory.PtExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumAdelicReadingEqOfTwoBaseChangeDecompsOnCover
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverBCRead

theorem evR_sum_eq {D : D7} (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (C : Cover T j σ)
    (hσ : C.σ₂.comp C.inc = σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {m m' : ℕ} (x : Fin m → C.c'.F)
    (f : Fin m → T.R j) (as : Fin m' → C.c'.F) (fs : Fin m' → T.R j)
    (hf : ∀ b, f b ∈ sec (T.Q.Xo j) T.Q.c a n)
    (hBC : IsBC C.hle (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) as fs)
    (y : FrPt (T.Q.Xo j) T.Q.c (CAt σ)) :
    (∑ b, C.σ₂ (C.d.eF (x b)) * toC (evR (T.Q.Xo j) T.Q.c (f b) y)) =
      ∑ i, C.σ₂ (C.d.eF (as i)) * toC (evR (T.Q.Xo j) T.Q.c (fs i) y) := by
  letI : Algebra C.c'.F (CAt σ) := (C.σ₂.comp (C.d.eF : C.c'.F →+* C.d.c₂.F)).toAlgebra
  have hA : AlgOver T.Q.c C.c' C.hle (CAt σ) := by
    intro c0
    show C.σ₂ (C.d.eF (incF T.Q.c C.c' C.hle c0)) = σ c0
    exact RingHom.congr_fun hσ c0
  have h1 := hBC (CAt σ) hA (FrPt.ext C.hle hA y)
  rw [Formalism.L2.Pj.evR_sum_smul] at h1
  simp only [GlobalTheory.FieldBCModel.evR_rulBC C.hle (hf _).1 hA, FrPt.res_ext] at h1
  exact h1

theorem phiJ_sum_eq_of_isBC : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (C : Cover T j σ), C.σ₂.comp C.inc = σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (m m' : ℕ) (x : Fin m → C.c'.F) (f : Fin m → T.R j) (as : Fin m' → C.c'.F) (fs : Fin m' → T.R j), (∀ b, f b ∈ sec (T.Q.Xo j) T.Q.c a n) → IsBC C.hle (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) as fs → ∑ b, C.σ₂ (C.d.eF (x b)) • T.phiJ j σ a (f b) = ∑ i, C.σ₂ (C.d.eF (as i)) • T.phiJ j σ a (fs i) := by
  intro D T j σ C hσ a n m m' x f as fs hf hBC
  have key : (∑ b, C.σ₂ (C.d.eF (x b)) • rdU (T.U j σ) (f b) : FDSec (T.U j σ).X) =
      ∑ i, C.σ₂ (C.d.eF (as i)) • rdU (T.U j σ) (fs i) := by
    funext k z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h : z ∈ ((T.U j σ).X k).dom
    · simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos h]
      exact evR_sum_eq T j σ C hσ a n x f as fs hf hBC ((T.U j σ).un k ⟨z, h⟩)
    · simp [rdU, dif_neg h]
  let L : FDSec (T.U j σ).X →ₗ[ℂ] (GA D (T.V j σ) → ℂ) := (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
    adel (T.V j σ) (T.dict j σ) (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) (T.cE j σ))
  have e : ∀ g : T.R j, T.phiJ j σ a g = L (rdU (T.U j σ) g) := fun _ => rfl
  simp only [e, ← map_smul, ← map_sum, key]

end GlobalTheory.CoverBCRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSupportCompatibleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_support_compatible : GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), IsRc hL T I rc → ∀ k v, TameGen.SupportCompat (fun a => D.naut.inePol a (D.ntypes.tg k v)) (fun π : Supp.GLRep _ => rc k v π.1 π.2) := by
  first | exact @GlobalTheory.SerSys.SuppTame.supportCompat | exact GlobalTheory.SerSys.SuppTame.supportCompat | (intros; apply GlobalTheory.SerSys.SuppTame.supportCompat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValSubLtIff
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DelEps
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DelEps.WeilRes

open Pointwise

variable {Ω : Type} [Field Ω]

theorem mem_Dec_iff {F : Type} [Field F] [NumberField F] [Algebra F Ω] {A : ValuationSubring Ω} {σ : G F Ω} :
    σ ∈ Dec (F := F) A ↔ ∀ x, (σ x ∈ A ↔ x ∈ A) := by
  refine ⟨fun h x => apply_mem_iff_of_mem_Dec h x, fun h => ?_⟩
  show σ • A = A
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← h, mul_inv_apply]

theorem normV_eq_pow {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

theorem under_eq {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v)
    (h' : IsPlaceOver A w) : w.under (𝓞 K) = v := by
  refine eq_of_isPlaceOver (A := A) ?_ h
  intro x
  show _ ↔ algebraMap (𝓞 K) (𝓞 L) x ∈ w.asIdeal
  rw [← h' (algebraMap (𝓞 K) (𝓞 L) x), IsScalarTower.algebraMap_apply K L Ω]
  rfl

theorem val_le_one {L : Type} [Field L] [NumberField L] [Algebra L Ω] (A : ValuationSubring Ω) (x : 𝓞 L) :
    A.valuation (algebraMap L Ω x) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A ((x.isIntegral_coe).algebraMap))

section Res

variable {L : Type} [Field L] [NumberField L] [Algebra L Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}

end Res

end GlobalTheory.DelEps.WeilRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightSectionEqZeroOfVanishingFiniteExtensionsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightSection_eq_zero_of_vanishing_finite_extensions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : Rul Xo c), h ∈ sec Xo c a n → (∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (y : FrPt Xo c L), evR Xo c h y = 0) → h = 0 := by
  first | exact @GlobalTheory.Reg.sec_eq_zero_of_finite_values | exact GlobalTheory.Reg.sec_eq_zero_of_finite_values | (intros; apply GlobalTheory.Reg.sec_eq_zero_of_finite_values <;> assumption)
end

