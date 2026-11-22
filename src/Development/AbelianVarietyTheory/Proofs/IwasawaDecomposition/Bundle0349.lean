import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0170
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNe
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0009
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOMulSource
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactActsOnRealVacuaByDetPowers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyFinOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.FitRho

open Formalism.L2.NR

def castQ {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) : Qbar p ≃+* Qbar q := by
  subst h; exact RingEquiv.refl _

theorem exists_heq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (z : ℤ_[p]) : ∃ z' : ℤ_[q], HEq z z' := by
  subst h; exact ⟨z, HEq.rfl⟩

theorem castQ_alg {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (z : ℤ_[p]) (z' : ℤ_[q]) (hz : HEq z z') :
    (castQ h).symm (algebraMap ℚ_[q] (Qbar q) (z' : ℚ_[q])) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p]) := by
  subst h
  obtain rfl := eq_of_heq hz
  rfl

theorem mapRep_mapRep {Γ A B C : Type} [Group Γ] [CommRing A] [CommRing B] [CommRing C] {n : ℕ} (f : A →+* B)
    (g : B →+* C) (ρ : Γ →* GL (Fin n) A) : mapRep g (mapRep f ρ) = mapRep (g.comp f) ρ := by
  ext x i j
  rfl

theorem isRepOf_cast (D : D7) {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (ι : Qbar q ≃+* ℂ) {n : ℕ}
    (π : D.naut.CG n) (s : ℝ) (ρ : G D.host.E D.nd.Om →* GL (Fin n) (Qbar q))
    (hρ : IsRepOf D p ((castQ h).trans ι) π s (mapRep (castQ h).symm.toRingHom ρ)) : IsRepOf D q ι π s ρ := by
  subst h
  have e1 : (castQ (rfl : p = p)).trans ι = ι := by ext x; rfl
  have e2 : mapRep (castQ (rfl : p = p)).symm.toRingHom ρ = ρ := by ext g i j; rfl
  rw [e1, e2] at hρ
  exact hρ

theorem conj_of_isRepOf (D : D7) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (π : D.naut.CG n) (s : ℝ)
    (hC : GlobalTheory.RowTie.ChebSplit D.nd) (ρ₁ ρ₂ : G D.host.E D.nd.Om →* GL (Fin n) (Qbar l))
    (h₁ : IsRepOf D l ι π s ρ₁) (h₂ : IsRepOf D l ι π s ρ₂) : IsConjRep ρ₁ ρ₂ := by
  obtain ⟨c₁, s₁, f₁⟩ := h₁
  obtain ⟨c₂, s₂, f₂⟩ := h₂
  have hfin := (Filter.eventually_cofinite.mp f₁).union (Filter.eventually_cofinite.mp f₂)
  have hcp := GlobalTheory.TwistLG.charpoly_eq_of_dense ρ₁ ρ₂ c₁ c₂ _ (hC hfin.toFinset).closure_eq (by
    rintro g ⟨w, hw, -, B, hB, hg⟩
    rw [Set.Finite.mem_toFinset] at hw
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hw
    apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [hw.1 B g hB hg, hw.2 B g hB hg])
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ₂ ρ₁ s₂ s₁ (fun g => (hcp g).symm)
  exact ⟨P⁻¹, fun g => by rw [hP g, inv_inv]⟩

theorem charpoly_fin_one {k : Type} [CommRing k] (M : Matrix (Fin 1) (Fin 1) k) : M.charpoly = X - C (M 0 0) := by
  rw [Matrix.charpoly, Matrix.det_unique, Matrix.charmatrix_apply_eq]
  rfl

theorem rhoOfRow_isRepOf (D : D7) (hG : GalRepEx D) (hC : ClassFieldHeckeAlgebraic D) (hη : EtaShiftInt D) (a : D.nd.Loc)
    (π : D.naut.CG D.R.r) (hc : D.naut.csd π) (hr : D.naut.ralg π) :
    IsRepOf D (D.nd.l a) (D.naut.iotaQC a) (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2)
      (rhoOfRow D hG hC hη a π hc hr) := by
  obtain ⟨c1, ss1, f1⟩ := rowRho_spec D hG a π hc hr
  obtain ⟨cχ, awayχ, -⟩ := Classical.choose_spec (hC a D.naut.etaTinv (-(D.R.t : ℝ) / 2) hη)
  set χ1 := Classical.choose (hC a D.naut.etaTinv (-(D.R.t : ℝ) / 2) hη) with hχ1
  have e0 : rhoOfRow D hG hC hη a π hc hr =
      Formalism.MainNotions.SumRepresentations.At.twGL (rowRho D hG a π hc hr) (Matrix.GeneralLinearGroup.det.comp χ1) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e0]; exact GlobalTheory.TwistLG.cont_twGL _ _ c1 cχ
  · rw [e0]; exact GlobalTheory.TwistLG.isSSRep_twGL _ _ ss1
  have hfin := placesOver_finite D.host.E (D.nd.l a) (Fact.out : (D.nd.l a).Prime).ne_zero
  filter_upwards [f1, D.naut.locG_unr_ae π, hfin.compl_mem_cofinite] with w hw1 hu hwl
  intro B σ hB hσ
  have hwl' : w ∉ placesOver D.host.E (D.nd.l a) := hwl

  have hue : D.naut.unr (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) :=
    (D.naut.unr_tw _ _).2 (D.naut.etaTinv_def w).1
  obtain ⟨u, hu1⟩ : ∃ u, D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) = {u} := by
    apply Multiset.card_eq_one.mp
    rw [D.naut.frobEig_tw _ _ (D.naut.etaTinv_def w).1, Multiset.card_map,
      D.naut.frobEig_card _ (D.naut.etaTinv_def w).1, D.naut.locG_dim]
  have hwd := D.naut.wdOf_frob a χ1 w hwl' cχ (by rw [awayχ w hwl']; exact hue) B σ hB hσ
  rw [awayχ w hwl', hu1, Multiset.map_singleton, Multiset.prod_singleton, charpoly_fin_one, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C] at hwd
  have hχu : D.naut.iotaQC a ((Matrix.GeneralLinearGroup.det.comp χ1 σ : (Qbar (D.nd.l a))ˣ) : Qbar (D.nd.l a)) = u := by
    have := congrArg (Polynomial.coeff · 0) hwd
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub, neg_inj] at this
    show D.naut.iotaQC a ((χ1 σ : Matrix (Fin 1) (Fin 1) _).det) = u
    rw [Matrix.det_unique]
    exact this

  have h1 := hw1 B σ hB hσ
  rw [isoLoc_single] at h1
  rw [e0, GlobalTheory.TwistLG.twGL_val, ← Matrix.charpoly_map, GlobalTheory.ParamRep.map_smul_matrix,
    GlobalTheory.ParamRep.galPol_twist D.nd D.naut π hu u hu1]
  have h2 : ((((rowRho D hG a π hc hr) σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).map
      (D.naut.iotaQC a).toRingHom).charpoly =
      ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2))).map fun α => X - C α).prod := by
    rw [Matrix.charpoly_map]; exact h1
  have h3 := GlobalTheory.ParamRep.charpoly_smul_of_prod _ u _ h2
  have hχu' : (D.naut.iotaQC a).toRingHom ((Matrix.GeneralLinearGroup.det.comp χ1 σ : (Qbar (D.nd.l a))ˣ) :
      Qbar (D.nd.l a)) = u := hχu
  rw [hχu']
  exact h3

end GlobalTheory.HeightCounting.FitRho

namespace GlobalTheory.HeightCounting.FitRho

open Formalism.L2.NR

theorem fracMap_eq {O0 O : Type} [CommRing O0] [IsDomain O0] [ValuationRing O0] [CommRing O] [IsDomain O]
    (f : O0 →+* O) (hf : Function.Injective f) {F : Type} [Field F] (e : F →+* FractionRing O0)
    (e' : F →+* FractionRing O) (h : ∀ x y, algebraMap O0 _ y = e x → e' x = algebraMap O _ (f y)) (x : F) :
    GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf (e x) = e' x := by
  rcases ValuationRing.isInteger_or_isInteger O0 (e x) with ⟨y, hy⟩ | ⟨y, hy⟩
  · rw [← hy, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg, h x y hy]
  · have hy' : algebraMap O0 (FractionRing O0) y = e x⁻¹ := by rw [map_inv₀]; exact hy
    have h1 := h x⁻¹ y hy'
    have h2 : e x = (algebraMap O0 (FractionRing O0) y)⁻¹ := by rw [hy, inv_inv]
    rw [h2, map_inv₀, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg, ← h1, map_inv₀, inv_inv]

end GlobalTheory.HeightCounting.FitRho

namespace GlobalTheory.HeightCounting.FitRho

open Formalism.L2.NR

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem rhoS_withLoc (hL : GlobalTheory.Published.LocalLanglandsGL) (D' : D7) (b : NBuilt hL D')
    (hcheb : GlobalTheory.RowTie.ChebSplit b.D.nd) (hP : RowPar (withLoc b.L)) (hG : GalRepEx (withLoc b.L))
    (hC : ClassFieldHeckeAlgebraic (withLoc b.L)) (hη : EtaShiftInt (withLoc b.L)) (a : (withLoc b.L).nd.Loc)
    (s : (withLoc b.L).ntw.Sig ((withLoc b.L).ntw.twOf a))
    (hs : (withLoc b.L).ntw.side _ s = (withLoc b.L).ntw.twSide a) (hj : (withLoc b.L).ntw.jS _ s = (withLoc b.L).nd.j a) :
    ∃ (σ : (withLoc b.L).what₂.FT) (hσ : (withLoc b.L).what₂.isot ((withLoc b.L).nd.j a) σ ≠ ⊥)
      (hg : (withLoc b.L).nd.goodRow σ),
      ∀ (π : (withLoc b.L).naut.CG (withLoc b.L).R.r) (hS : rowSig (withLoc b.L) a σ = [⟨(withLoc b.L).R.r, π, 1⟩]),
        IsConjRep (Formalism.MainNotions.N.mapRep ((Formalism.MainNotions.N.iotaOQ (withLoc b.L).nd (withLoc b.L).naut a).comp ((withLoc b.L).ntw.twist₂ a))
            ((withLoc b.L).ntw.rhoS _ s))
          (rhoOfRow (withLoc b.L) hG hC hη a π (rowSig_csd_ralg (withLoc b.L) hP a σ hσ hg π hS).1
            (rowSig_csd_ralg (withLoc b.L) hP a σ hσ hg π hS).2) := by
  obtain ⟨hiso, hgood, hspec⟩ := b.Bs.rhoS (b.L.T.twOf a) s
  have hσ : (withLoc b.L).what₂.isot ((withLoc b.L).nd.j a) (b.Bs.rowS (b.L.T.twOf a) s) ≠ ⊥ := by
    rw [← hj]; exact hiso
  refine ⟨b.Bs.rowS (b.L.T.twOf a) s, hσ, hgood, fun π hS => ?_⟩
  obtain ⟨hc, hr⟩ := rowSig_csd_ralg (withLoc b.L) hP a _ hσ hgood π hS

  have hloc : ∀ w, IsSplitPl b.D.host w → b.D.naut.locG π w = b.A.row.locR (b.Bs.rowS (b.L.T.twOf a) s) w := by
    intro w hw
    have h1 := (rowSig_spec (withLoc b.L) hP a _ hσ).2.2 w hw
    rw [hS] at h1
    exact ((isoLoc_single (withLoc b.L) π w).symm.trans h1).trans (b.Au.locW a _ w)

  have hpq : (withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a) = (withLoc b.L).nd.l a := (withLoc b.L).ntw.twOf_l a

  let φ0 : FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) →+* Qbar ((withLoc b.L).nd.l a) :=
    ((withLoc b.L).naut.iotaQ a).comp (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap ((withLoc b.L).ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.twO_inj (withLoc b.L).ntw a))
  have hφ0 : φ0.comp (algebraMap ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) (FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)))) =
      (Formalism.MainNotions.N.iotaOQ (withLoc b.L).nd (withLoc b.L).naut a).comp ((withLoc b.L).ntw.twist₂ a) := by
    ext y
    show (withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ (algebraMap _ _ y)) =
      (withLoc b.L).naut.iotaQ a (algebraMap _ _ ((withLoc b.L).ntw.twist₂ a y))
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg]
  have hemb : ∀ x : ↥b.D.LL0, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap ((withLoc b.L).ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.twO_inj (withLoc b.L).ntw a)
      ((if (withLoc b.L).ntw.twSide a then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a) else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a)) x) =
      (withLoc b.L).nd.embK a (x : b.D.what₂.LL) :=
    fracMap_eq ((withLoc b.L).ntw.twist₂ a) _ (if (withLoc b.L).ntw.twSide a then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a) else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a))
      (((withLoc b.L).nd.embK a).comp (algebraMap ↥b.D.LL0 b.D.what₂.LL)) (fun x y hy => (withLoc b.L).ntw.twO_emb a x y hy)
  let φ := (castQ hpq).symm.toRingHom.comp φ0
  let ι := (castQ hpq).trans ((withLoc b.L).naut.iotaQC a)
  have hφ : ∀ z : ℤ_[(withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)], φ (algebraMap ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) (FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a))) (algebraMap ℤ_[(withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)] ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) z)) =
      algebraMap ℚ_[(withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)] (Qbar ((withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a))) (z : ℚ_[(withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)]) := by
    intro z
    obtain ⟨z', hz⟩ := exists_heq hpq z
    show (castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ (algebraMap ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) (FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a))) (algebraMap ℤ_[((withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a))] ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) z)))) = _
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg]
    erw [b.Sp.twO_alg a z z' hz, (withLoc b.L).naut.iotaQ_alg a z']
    exact castQ_alg hpq z z' hz
  have hι : ∀ x : ↥b.D.LL0, ι (φ ((if (withLoc b.L).ntw.side ((withLoc b.L).ntw.twOf a) s then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a)
      else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a)) x)) = embLL0 b.D x := by
    intro x
    have hs' : (withLoc b.L).ntw.side ((withLoc b.L).ntw.twOf a) s = (withLoc b.L).ntw.twSide a := hs
    rw [hs']
    show (withLoc b.L).naut.iotaQC a ((castQ hpq) ((castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ _)))) = _
    rw [RingEquiv.apply_symm_apply, hemb x]
    exact (withLoc b.L).naut.iota_LL a _
  have hR := hspec π hc hr hloc φ ι hφ hι
  have hR' : IsRepOf (withLoc b.L) ((withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)) ((castQ hpq).trans ((withLoc b.L).naut.iotaQC a))
      ((withLoc b.L).naut.tw π (withLoc b.L).naut.etaTinv) ((1 - ((withLoc b.L).R.nV : ℝ)) / 2)
      (Formalism.MainNotions.N.mapRep (castQ hpq).symm.toRingHom (Formalism.MainNotions.N.mapRep
        ((Formalism.MainNotions.N.iotaOQ (withLoc b.L).nd (withLoc b.L).naut a).comp ((withLoc b.L).ntw.twist₂ a))
        ((withLoc b.L).ntw.rhoS _ s))) := by
    rw [← hφ0, mapRep_mapRep]
    exact hR
  exact conj_of_isRepOf (withLoc b.L) ((withLoc b.L).naut.iotaQC a) _ _ hcheb _ _
    (isRepOf_cast (withLoc b.L) hpq _ _ _ _ hR') (rhoOfRow_isRepOf (withLoc b.L) hG hC hη a π _ _)

end GlobalTheory.HeightCounting.FitRho

namespace GlobalTheory.HeightCounting

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem nRhoTied_withLoc : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D' : D7) (b : NBuilt hL D'), (∀ x : b.D.LL0, star (x : b.D.what₂.LL) ∈ b.D.LL0) → (∀ j g, ∃ z : ℤ, eExp b.D j g = z) → (∀ v, v ∈ placesOver b.D.host.E b.D.host.pde ∨ v ∈ placesOver b.D.host.E b.D.host.pde' → IsSplitPl b.D.host v) → GlobalTheory.RowTie.ChebSplit b.D.nd → TypesOpen (withLoc b.L) b.jE → NR.NRhoTied (withLoc b.L) := by
  intro hL D' b _ _ _ hcheb hT
  exact ⟨hT.rbarSS, hT.rbar, fun hP hG hC hη a s hs hj =>
    FitRho.rhoS_withLoc hL D' b hcheb hP hG hC hη a s hs hj⟩

end GlobalTheory.HeightCounting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMapRep
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HeightCounting.PhtExt

variable {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut}

theorem continuous_mapRep {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A B : Type} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] {a : ℕ} (f : A →+* B) (hf : Continuous f) (ρ : Γ →* GL (Fin a) A)
    (hρ : Continuous fun g => ((ρ g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A)) :
    Continuous fun g => ((mapRep f ρ g : GL (Fin a) B) : Matrix (Fin a) (Fin a) B) := by
  have : (fun g => ((mapRep f ρ g : GL (Fin a) B) : Matrix (Fin a) (Fin a) B)) =
      fun g => ((ρ g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A).map f := by
    funext g; rfl
  rw [this]
  exact hρ.matrix_map hf

end GlobalTheory.HeightCounting.PhtExt

namespace GlobalTheory.HeightCounting.PhtExt

variable {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut}

noncomputable def ext (Wd₀ : WDSide D T) : WDSide D T :=
  { Wd₀ with
    IsdRW := fun l _ ι a r w =>
      (Continuous fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧ Wd₀.IsdRW l ι r w
    wdOf_unrL := fun l _ ι _ r w hw hc hd => Wd₀.wdOf_unrL l ι r w hw hc hd.2
    wdOf_mono0L := fun l _ ι _ r w hw hc hd => Wd₀.wdOf_mono0L l ι r w hw hc hd.2
    loc := by
      intro l _ ι w hw O _ _ _ Bw hB φ hφ
      obtain ⟨h1, h2⟩ := Wd₀.loc l ι w hw O Bw hB φ hφ
      have hφc : Continuous φ := by
        have e : (φ : O → Qbar l) = fun x => ((Bw.toLL x : ↥Bw.LL.1) : Loc.Om l) := funext hφ
        rw [e]
        unfold LocBridge.toLL
        exact continuous_subtype_val.comp (continuous_subtype_val.comp Bw.eO_cont)
      refine ⟨fun m ρ hρ => ?_, fun LL' hLL' m ρ hρ => ?_⟩
      · obtain ⟨c1, c2, c3, c4⟩ := h1 m ρ hρ
        exact ⟨c1, (and_iff_right (continuous_mapRep φ hφc ρ hρ)).trans c2, c3, c4⟩
      · have hf : Continuous (algebraMap ↥LL'.1 (Qbar l)) := continuous_subtype_val
        obtain ⟨c1, c2, c3, c4⟩ := h2 LL' hLL' m ρ hρ
        exact ⟨c1, (and_iff_right (continuous_mapRep _ hf ρ hρ)).trans c2, c3, c4⟩ }

theorem exists_phtOn_all : PhtCmp → ∀ (D : D7) (fr : OmFrame D) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), WDSide D T →
    ∃ Wd : WDSide D T, PhtOn Wd fr fun _ _ _ _ => True := by
  intro hP D fr T Wd₀
  exact ⟨ext Wd₀, ⟨fun l _ ι a r τ w _ hw hd => (hP D fr T Wd₀).card l ι a r τ w hd.1 hw hd.2⟩⟩

end GlobalTheory.HeightCounting.PhtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryRealPointsActFockSubstitution
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLift.FockAct

open GlobalTheory.AdTh.SourceBasis GlobalTheory.OrientedHeis

theorem unitMap_mul_mul {m n : ℕ} (B U : Matrix (Fin n) (Fin n) ℂ) (B' H : Matrix (Fin m) (Fin m) ℂ) (i : Fin m)
    (j : Fin n) : unitMap (B * U) (B' * H) i j = ∑ i', ∑ c, (H i' i * U⁻¹ j c) • unitMap B B' i' c := by
  have e : H * Matrix.single i j (1 : ℂ) * U⁻¹ = ∑ i', ∑ c, (H i' i * U⁻¹ j c) • Matrix.single i' c (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single (H * Matrix.single i j (1 : ℂ) * U⁻¹)]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
    congr 1
    rw [Matrix.mul_apply, Finset.sum_eq_single j (fun c _ hc => by simp [Matrix.mul_single_apply_of_ne, hc]) (by simp)]
    simp
  unfold unitMap
  calc _ = B' * (H * Matrix.single i j (1 : ℂ) * U⁻¹) * B⁻¹ := by
        rw [Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [e, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}

theorem pureTensorO_mul_mul (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (BV U : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (BW H : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (P : Pol D.what₂.Tau W.rank V.rank) :
    pureTensorO ψ θ V W (fun _ => 1) (fun _ => 1) (fun τ => BV τ * U τ) (fun τ => BW τ * H τ) f P =
      pureTensorO ψ θ V W (fun _ => 1) (fun _ => 1) BV BW f (subst (fun τ => (U τ)⁻¹) H P) := by
  have hadd : ∀ f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → IsThetaFunO ψ V W (f + f') := fun _ _ => theta_add
  have hsm : ∀ (a : ℂ) f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (a • f) := fun a _ => theta_smul a
  have hA : ∀ (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
      (BT : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) i f, IsThetaFunO ψ V W f →
      IsThetaFunO ψ V W (aPlusAll (heisO ψ V W) θ (fun _ => cplxO 1 1) BS BT i f) :=
    fun _ _ _ _ h => aPlus_th hψ hθ _ _ _ h
  have hm : ∀ (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
      (BT : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) Q,
      IsThetaFunO ψ V W (pureTensorO ψ θ V W (fun _ => 1) (fun _ => 1) BS BT f Q) := fun BS BT Q =>
    GlobalTheory.Ker.FockAlg.pure_mem (P := IsThetaFunO ψ V W) hadd hsm (hA BS BT) hf Q
  have hX : ∀ (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
      (BT : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) Q v,
      pureTensorO ψ θ V W (fun _ => 1) (fun _ => 1) BS BT f (MvPolynomial.X v * Q) =
        aPlusAll (heisO ψ V W) θ (fun _ => cplxO 1 1) BS BT v
          (pureTensorO ψ θ V W (fun _ => 1) (fun _ => 1) BS BT f Q) :=
    fun BS BT Q v => GlobalTheory.Ker.FockAlg.pure_X_mul (A := aPlusAll (heisO ψ V W) θ (fun _ => cplxO 1 1) BS BT)
      (P := IsThetaFunO ψ V W) hadd hsm (hA BS BT)
      (fun i j _ h => aPlus_comm hψ hθ i.1 _ (s := fun _ => 1) (fun τ => by simp) (fun τ => by simp) j.1 _ h)
      (fun _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h') (fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h) hf Q v
  have h1 := fun BS BT => GlobalTheory.FiniteFock.pureTensorO_one ψ θ V W (fun _ => 1) (fun _ => 1) BS BT f
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, ← mul_one (MvPolynomial.C a), ← MvPolynomial.smul_eq_C_mul,
      map_smul, map_smul, h1, h1]
  | add P Q hP hQ => rw [map_add, map_add, map_add, hP, hQ]
  | mul_X P v hP =>
    obtain ⟨τ, i, j⟩ := v
    rw [mul_comm, hX, hP, map_mul]
    clear hP
    generalize (subst _ H P : Pol D.what₂.Tau W.rank V.rank) = Q
    rw [subst, MvPolynomial.aeval_X]
    simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, hX]
    simp only [aPlusAll, aPlus]
    rw [unitMap_mul_mul, crea_sum hψ hθ _ (hm _ _ _), Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [crea_sum hψ hθ _ (hm _ _ _), Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [crea_smul hψ hθ τ _ (hm _ _ _) _ True (by simp), if_pos trivial, smul_comm]

theorem om_vac {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hω : IsWeilDatumO ψ V W χS χT ω) (hθ : IsInfFam θ) (kV : V.SigOK) (kW : W.SigOK)
    {sS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D V τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D W τ) (sT τ))
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hv : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (sS τ) (sT τ)) f) {g : GA D V} (hg : g ∈ GinfC V)
    {h : GA D W} (hh : h ∈ GinfC W)
    (cS : ∀ τ, sS τ * compAt θ τ (Formalism.L2.Theta.mt V g) = compAt θ τ (Formalism.L2.Theta.mt V g) * sS τ)
    (cT : ∀ τ, sT τ * compAt θ τ (Formalism.L2.Theta.mt W h) = compAt θ τ (Formalism.L2.Theta.mt W h) * sT τ) :
    ∃ c : ℂ, ω (g, h) f = c • f := by
  have dS := GlobalTheory.PlaceModel.isSelfDualC_latFrame V
  have dT := GlobalTheory.PlaceModel.isSelfDualC_latFrame W
  obtain ⟨f₀, h₀⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hω.std hθ V W sS sT kV kW hS hT _ _ dS dT
  have h1 := GlobalTheory.WeilVacMove.isVacO_om D ψ θ V W χS χT ω hω hθ sS sS sT sT _ _ _ _ g h cS cT
    (fun u => ⟨fun hu => ⟨u, hu, (GlobalTheory.VacuumChar.actO_fin hg hh (GlobalTheory.SplitScalar.latO_fin hu)).symm⟩,
      fun ⟨u₀, hu, e⟩ => by rwa [e, GlobalTheory.VacuumChar.actO_fin hg hh (GlobalTheory.SplitScalar.latO_fin hu)]⟩) f₀ h₀
  obtain ⟨c, -, e⟩ := GlobalTheory.VacUnique.vacUniqueO D ψ θ hω.std hθ V W sS sT kV kW hS hT _ _ dS dT f₀ _ h₀ h1
  refine ⟨c, ?_⟩
  have hs := GlobalTheory.VacuumChar.mem_span kV kW hS hT dS dT h₀ (f := f) ⟨hf, hv⟩
  clear hf hv
  induction hs using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨x, rfl⟩ := hx
    show ω (g, h) (heisO ψ V W x f₀) = c • heisO ψ V W x f₀
    rw [hω.om_heis g h _ _ h₀.2.theta, GlobalTheory.VacuumChar.actO_fin hg hh x.2, e, GlobalTheory.SplitScalar.heisO_smul]
  | zero => rw [map_zero, smul_zero]
  | add a b _ _ ha hb => rw [map_add, ha, hb, smul_add]
  | smul r a _ ha => rw [map_smul, ha, smul_comm]

open Classical in
theorem compAt_atTau {S : D.what₂.Tau → SPar} {M : DSModel V S} (hθ : IsInfFam θ) (h : AllPlus M) (τ : D.what₂.Tau)
    (u : Matrix.unitaryGroup (Fin V.rank) ℂ) (ρ : D.what₂.Tau) :
    onb M ρ * (if ρ = τ then (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) else 1) =
      compAt θ ρ (Formalism.L2.Theta.mt V (atTau θ V τ (unfr M τ u))) * onb M ρ := by
  have s := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ (h.unfr_mem τ u)
  split_ifs with e
  · subst e
    have e1 : compAt θ ρ (Formalism.L2.Theta.mt V (atTau θ V ρ (unfr M ρ u))) = unfr M ρ u := s.2.1
    rw [e1, unfr, onb, Matrix.mul_nonsing_inv_cancel_right _ _ (fr_det M ρ)]
  · have e1 : compAt θ ρ (Formalism.L2.Theta.mt V (atTau θ V τ (unfr M τ u))) = 1 := s.2.2 ρ e
    rw [e1, Matrix.mul_one, Matrix.one_mul]

theorem compAt_one (B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (ρ : D.what₂.Tau) :
    B * 1 = compAt θ ρ (Formalism.L2.Theta.mt V 1) * B := by
  have e1 : compAt θ ρ (Formalism.L2.Theta.mt V 1) = 1 := GlobalTheory.PointAtPlaceHom.infMat_one V (θ ρ)
  rw [e1, Matrix.mul_one, Matrix.one_mul]

theorem om_ptOf {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    {S S' : D.what₂.Tau → SPar} {M : DSModel V S} {M' : DSModel W S'} {f : WO V W → ℂ}
    (hω : IsWeilDatumO ψ V W χS χT ω) (hθ : IsInfFam θ) (kV : V.SigOK) (kW : W.SigOK) (hM : AllPlus M)
    (hM' : AllPlus M') (hf : IsThetaFunO ψ V W f)
    (hv : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f) {g : GA D V} (hg : g ∈ GinfC V)
    {h : GA D W} (hh : h ∈ GinfC W) (U : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (H : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (hU : ∀ ρ, onb M ρ * U ρ = compAt θ ρ (Formalism.L2.Theta.mt V g) * onb M ρ)
    (hH : ∀ ρ, onb M' ρ * H ρ = compAt θ ρ (Formalism.L2.Theta.mt W h) * onb M' ρ) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ P, ω (g, h) (ptOf ψ θ M M' f P) = c • ptOf ψ θ M M' f (subst (fun ρ => (U ρ)⁻¹) H P) := by
  have e1 : cart M = fun _ => 1 := funext hM.cart
  have e2 : cart M' = fun _ => 1 := funext hM'.cart
  unfold ptOf
  rw [e1, e2] at hv ⊢
  obtain ⟨c, c0, hc⟩ : ∃ c : ℂ, c ≠ 0 ∧ ω (g, h) f = c • f := by
    by_cases f0 : f = 0
    · exact ⟨1, one_ne_zero, by rw [f0, map_zero, smul_zero]⟩
    obtain ⟨c, e⟩ := om_vac hω hθ kV kW (sS := fun _ => 1) (sT := fun _ => 1)
      (fun τ => ⟨by simp, by simp, by simpa using hM.posDef τ⟩) (fun τ => ⟨by simp, by simp, by simpa using hM'.posDef τ⟩)
      hf hv hg hh (fun τ => by simp) (fun τ => by simp)
    refine ⟨c, fun c0 => f0 ?_, e⟩
    rw [c0, zero_smul] at e
    have e' := congrArg (ω (g, h)⁻¹) e
    rwa [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at e'
  refine ⟨c, c0, fun P => ?_⟩
  rw [(om_pureTensorO D ψ θ V W χS χT ω hω hθ (fun _ => 1) (fun _ => 1) (onb M) (fun ρ => onb M ρ * U ρ)
    (fun _ => 1) (fun _ => 1) (onb M') (fun ρ => onb M' ρ * H ρ) g h (fun τ => by simp) (fun τ => by simp) hU hH f hf P).2,
    hc, GlobalTheory.FiniteFock.pureTensorO_smul, pureTensorO_mul_mul hω.std hθ _ _ _ _ hf]

theorem fock_act : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (θ : InfFam D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ), IsWeilDatumO ψ V W χS χT ω → IsInfFam θ → V.SigOK → W.SigOK → AllPlus M → AllPlus M' → IsThetaFunO ψ V W f → (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f) → ∀ τ, (∀ g : Matrix.unitaryGroup (Fin V.rank) ℂ, ∃ c : ℂ, c ≠ 0 ∧ ∀ P, ω (atTau θ V τ (unfr M τ g), 1) (ptOf ψ θ M M' f P) = c • ptOf ψ θ M M' f (colSub W.rank τ g P)) ∧ ∀ u : Matrix.unitaryGroup (Fin W.rank) ℂ, ∃ c : ℂ, c ≠ 0 ∧ ∀ P, ω (1, atTau θ W τ (unfr M' τ u)) (ptOf ψ θ M M' f P) = c • ptOf ψ θ M M' f (rowSub V.rank τ u P) := by
  classical
  intro D ψ V W χS χT ω θ S S' M M' f hω hθ kV kW hM hM' hf hv τ
  refine ⟨fun g => ?_, fun u => ?_⟩
  · have := om_ptOf hω hθ kV kW hM hM' hf hv (GlobalTheory.PointAtPlaceHom.atTau_mem V τ _) (one_mem _) _ (fun _ => 1)
      (compAt_atTau hθ hM τ g) (fun ρ => compAt_one _ ρ)
    have e : (fun ρ => (if ρ = τ then (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) else 1)⁻¹) =
        fun ρ => if ρ = τ then star (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) else 1 := by
      funext ρ
      split_ifs
      · exact Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 g.2)
      · exact inv_one
    rw [e] at this
    exact this
  · have := om_ptOf hω hθ kV kW hM hM' hf hv (one_mem _) (GlobalTheory.PointAtPlaceHom.atTau_mem W τ _) (fun _ => 1) _
      (fun ρ => compAt_one _ ρ) (compAt_atTau hθ hM' τ u)
    simp only [inv_one] at this
    exact this

end GlobalTheory.DefLift.FockAct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvRoots
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

section CapelliMinorMembership

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw)

def piCoef (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (u : Formalism.IndefR.NX.U D.nd) : ↥D.LL0 :=
  (Nat.card (Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ * (((psiUOf D.nd (NX.xiRed D) θ u)⁻¹ : (↥D.LL0)ˣ) : ↥D.LL0)

def eLop (j : ℕ) : Module.End D.what₂.LL (S.WL j) :=
  ∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g

def piLop (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ) : Module.End D.what₂.LL (S.WL j) :=
  ∑ᶠ u : Formalism.IndefR.NX.U D.nd, ((piCoef D θ u : ↥D.LL0) : D.what₂.LL) • actL D S j (u : G0g D.nd)

open Classical in

def evRoots (In : RatIn D S) (j k : ℕ) (P : PlE D.host) : Finset ↥D.LL0 :=
  (Finset.univ.filter fun σ : D.what₂.FT => D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ).image fun σ => In.eig j σ k P

def evPol (In : RatIn D S) (j k : ℕ) (P : PlE D.host) : Polynomial ↥D.LL0 :=
  ∏ r ∈ evRoots D S In j k P, (X - C r)

def phiLop (In : RatIn D S) (j k : ℕ) (P : PlE D.host) : Module.End D.what₂.LL (S.WL j) :=
  aeval (In.hL j k P) ((evPol D S In j k P).map (algebraMap ↥D.LL0 D.what₂.LL))

def hLT (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) :
    Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  (Module.End.baseChangeHom S.Ks (KT D T i b) ↥(WKr D S j) (hLr D S In j k P) :
    Module.End (KT D T i b) (KT D T i b ⊗[S.Ks] ↥(WKr D S j)))

def piKop (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) : Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  ∑ᶠ u : Formalism.IndefR.NX.U D.nd, readT D T i b (piCoef D In.θ u) • (actGT D T S In.rho In.chi i j b (u : G0g D.nd)).toLinearMap

def phiKop (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) :
    Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  aeval (hLT D T S In i j b k P) ((evPol D S In j k P).map (readT D T i b))

theorem hkT_eq (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) :
    hkT D T S In i j b k P = (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i)) ^ k • hLT D T S In i j b k P :=
  rfl

end CapelliMinorMembership

end GlobalTheory.HeightCounting.FormsStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
section
theorem GlobalTheory.globalArtinReciprocity_holds : GlobalTheory.Published.GlobalArtinReciprocity := CompanionTheory.FamInh.globalArtin
end

