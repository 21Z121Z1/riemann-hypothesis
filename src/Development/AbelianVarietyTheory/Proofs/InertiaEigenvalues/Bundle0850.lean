import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0181
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0837
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClassSystem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0842
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0845
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0813
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLocalGenerationInertPlaceOffLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0689

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealPointActsOnThetaFockVacuaByDetPower
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.RealVacPow

open scoped ComplexOrder

theorem vacuum_det_power : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ →
    ∀ (p : ℕ) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ τ, IsONBasis (gramAt D W τ) (sW τ) (BW τ) p) →
    ∃ k : D.what₂.Tau → ℤ, ∀ a ∈ GinfC V, ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f →
      (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (sW τ)) f) →
      om (a, 1) f = (∏ τ, (Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a)).det ^ k τ) • f := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP p BW hB
  have hP1 := hP.1
  obtain ⟨η, hη⟩ := hP1.eta
  choose b hb using hP1.expW
  have hsW : ∀ τ, IsCartanInv (gramAt D W τ) (sW τ) := hP.2.2.2.2.2.2.2.1
  choose q hq1 hq using fun τ => GlobalTheory.OneMapRef.RealMove.detPlus_one (n := V.rank) (sW τ) (hsW τ).1
  refine ⟨fun τ => -(b τ) - (q τ : ℤ), fun a ha f hf hv => ?_⟩
  have hθ : IsInfFam θ := hP1.inf
  have hψ := hP1.weil.std
  have hgV : ∀ τ, gramAt D V τ = 1 := fun τ => by
    unfold gramAt; rw [hP1.std]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hS : ∀ τ, IsCartanInv (gramAt D V τ) 1 := fun τ => by
    rw [hgV]; exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  have hdetV : ∀ τ, (gramAt D V τ).det ≠ 0 := fun τ => by rw [hgV]; simp
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ V hdetV a ha
  have mt1 : Formalism.L2.Theta.mt W 1 = 1 := by unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
  have hy : IsDetRoot W 1 1 := by
    unfold IsDetRoot
    have : ((matHom W 1).1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) = 1 := mt1
    rw [this, Matrix.det_one, one_mul, Units.val_one, map_one]
  have one : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt W 1) = 1 := fun τ => by
    rw [mt1]; exact Matrix.map_one _ (by simp) (by simp)
  rw [GlobalTheory.WeilVacChar.vacuum_character D ψ hψ V W θ hθ χV χW om η hη hP1.weil (fun _ => 1) sW hS hsW a ha 1 (one_mem _)
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, Matrix.one_mul, Matrix.mul_one]) x 1 hx hy f hf hv]
  congr 1
  have hexp : ∀ τ, HasInfExp D (χW * (η ^ W.rank)⁻¹) τ ((b τ : ℤ) : ℚ) := fun τ => by
    have := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (hb τ) (hη.2.2.2 τ) W.rank
    rwa [add_sub_cancel_right] at this
  have hνx := hxv _ b hexp
  have hinv : ∀ τ, (compAt θ τ (Formalism.L2.Theta.mt V a⁻¹)).det * (compAt θ τ (Formalism.L2.Theta.mt V a)).det = 1 := fun τ => by
    rw [GlobalTheory.OneMapRef.RealMove.det_compAt, GlobalTheory.OneMapRef.RealMove.det_compAt, ← map_mul, ← map_mul, ← Matrix.det_mul]
    have : Formalism.L2.Theta.mt V a⁻¹ * Formalism.L2.Theta.mt V a = 1 := by
      unfold Formalism.L2.Theta.mt; rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one]; rfl
    rw [this, Matrix.det_one, map_one, map_one]
  have hd0 : ∀ τ, (compAt θ τ (Formalism.L2.Theta.mt V a)).det ≠ 0 := fun τ h => by
    have := hinv τ; rw [h, mul_zero] at this; exact zero_ne_one this
  have hdp : ∀ τ, GlobalTheory.WeilParts.detPlus 1 (sW τ) (compAt θ τ (Formalism.L2.Theta.mt V a⁻¹)) (compAt θ τ (Formalism.L2.Theta.mt W 1)) =
      ((compAt θ τ (Formalism.L2.Theta.mt V a)).det)⁻¹ ^ q τ := fun τ => by
    rw [one, (hq τ _ 1 (by rw [Matrix.one_mul, Matrix.mul_one])).1]
    have e : (1 / 2 : ℂ) • (1 + sW τ) * 1 + (1 / 2 : ℂ) • (1 - sW τ) = 1 := by rw [Matrix.mul_one]; module
    rw [e, Matrix.det_one, one_pow, one_mul, eq_inv_of_mul_eq_one_left (hinv τ)]
  rw [map_one, mul_one, Circle.coe_inv, hνx, Finset.prod_congr rfl fun τ _ => hdp τ, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [zpow_sub₀ (hd0 τ), _root_.zpow_neg, zpow_natCast, inv_pow, div_eq_mul_inv]

end GlobalTheory.RealVacPow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupRelIffSameData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.Move

variable {D D' : D7}

scoped macro "set_cases " h1:ident h2:ident N:ident N':ident X:ident X':ident : tactic =>
  `(tactic| (
    obtain ⟨-, -, -, nOm, ninstOm, nalgOm, -, nPlG⟩ := $h1
    obtain ⟨-, xTw, -, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, -, -, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, -, xpD, -, -, -, -, -, -, fixedFieldTransport_initialPlaceSet_heq, -⟩ := $h2
    cases $N:ident; cases $N':ident
    dsimp only at nOm ninstOm nalgOm nPlG
    subst nOm; subst ninstOm; subst nalgOm; subst nPlG
    cases $X:ident; cases $X':ident
    dsimp only at xTw fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq xO xcrO xalgO xOk xcrOk xalgOk xpD fixedFieldTransport_initialPlaceSet_heq
    subst xTw; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xpD
    subst fixedFieldTransport_initialPlaceSet_heq))

theorem exists_setupRel (h : SameGeo D D') {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    (h1 : GlobalTheory.TwistChoice.SameGalois N N') (h2 : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients X X') (ρ : Setup X) :
    ∃ ρ' : Setup X', SetupRel ρ ρ' := by
  geo_cases h D D'
  set_cases h1 h2 N N' X X'
  obtain ⟨rc, ch, bad, e, ek, B, om, Cl, rep, β, eG⟩ := ρ
  rename_i fin
  refine ⟨@Setup.mk _ _ _ ⟨rc.κ, rc.art⟩ ch bad e ek
    (fun i j b => ⟨(B i j b).hr, ⟨(B i j b).F.ψ, (B i j b).F.θ, (B i j b).F.sT, (B i j b).F.BS, (B i j b).F.BT, (B i j b).F.ΛS,
      (B i j b).F.ΛT, (B i j b).F.βS, (B i j b).F.βT, (B i j b).F.f₀⟩, ⟨(B i j b).G.Pg, (B i j b).G.P, (B i j b).G.mu⟩,
      ⟨(B i j b).de.Q, (B i j b).de.chi, (B i j b).de.res⟩,
      ⟨(B i j b).w.p, (B i j b).w.q, (B i j b).w.ap, (B i j b).w.am, (B i j b).w.c, (B i j b).w.lam⟩, (B i j b).mu0, (B i j b).eta⟩)
    om (fun i j b t => Cl i j b ⟨t.Q, t.chi, t.res⟩) (fun i j b t => fin i j b ⟨t.Q, t.chi, t.res⟩)
    (fun i j b t => rep i j b ⟨t.Q, t.chi, t.res⟩) β eG,
    ⟨.rfl, .rfl⟩, .rfl, .rfl, .rfl, .rfl, ?_, .rfl, ?_, ?_, .rfl, ?_⟩
  · intro i i' hi j j' hj b
    cases hi; cases Fin.ext hj
    exact ⟨⟨.rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl⟩, ⟨.rfl, .rfl, .rfl⟩, ⟨.rfl, .rfl, .rfl⟩,
      ⟨.rfl, .rfl, .rfl, .rfl, .rfl, .rfl⟩, .rfl, .rfl⟩
  · rintro i i' hi j j' hj b ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨r1, r2, r3⟩
    cases hi; cases Fin.ext hj; cases r1; cases r2; cases r3
    rfl
  · rintro i i' hi j j' hj b ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨r1, r2, r3⟩
    cases hi; cases Fin.ext hj; cases r1; cases r2; cases r3
    exact HEq.rfl
  · intro i i' hi j j' hj b
    cases hi; cases Fin.ext hj
    exact HEq.rfl

theorem RecipRel.good (h : SameGeo D D') {Ω Ω' : Type} [i1 : Field Ω] [i2 : Algebra D.host.E Ω] [i1' : Field Ω']
    [i2' : Algebra D'.host.E Ω'] (hΩ : Ω = Ω') (h1 : HEq i1 i1') (h2 : HEq i2 i2') {a : Recip D Ω} {a' : Recip D' Ω'}
    (r : RecipRel a a') (g : a.Good) : a'.Good := by
  geo_cases h D D'
  subst hΩ; subst h1; subst h2
  obtain ⟨κ, art⟩ := a
  obtain ⟨κ', art'⟩ := a'
  obtain ⟨r1, r2⟩ := r
  cases r1; cases r2
  exact ⟨g.1, g.2, g.3, g.4⟩

theorem SetupRel.good_of (h : SameGeo D D') {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    (h1 : GlobalTheory.TwistChoice.SameGalois N N') (h2 : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients X X') (hδ : HEq X.delta X'.delta)
    (he : ∀ i i', HEq i i' → ∀ b x', ∃ x, HEq (sideEmb X i b x) (sideEmb X' i' b x') ∧ embLL0 D x = embLL0 D' x')
    {ρ : Setup X} {ρ' : Setup X'} (r : SetupRel ρ ρ') (g : ρ.Good) : ρ'.Good := by
  have grc := r.rc.good h (eq_of_heq h1.Om) h1.instOm h1.algOm g.rc
  have h0 := h
  geo_cases h D D'
  set_cases h1 h2 N N' X X'
  dsimp only at hδ
  subst hδ
  obtain ⟨⟨κ, art⟩, ch, bad, e, ek, B, om, Cl, rep, β, eG⟩ := ρ
  obtain ⟨⟨κ', art'⟩, ch', bad', e', ek', B', om', Cl', rep', β', eG'⟩ := ρ'
  obtain ⟨⟨r1, r2⟩, r3, r4, r5, r6, r7, r8, r9, r10, -, -⟩ := r
  dsimp only at r1 r2 r3 r4 r5 r6 r8
  subst r1 r2 r3 r4 r5 r6 r8
  refine ⟨grc, fun i => ⟨(g.ch i).1, (g.ch i).2⟩, g.bad_ne, g.goodSetup_bad_mem_badPlaces, g.goodSetup_badPlaces_conj, g.goodSetup_placesOverTwo_subset, g.goodSetup_count_eq_zero_off_badPlaces, fun i b x' => ?_, g.ek_e,
    fun i j b => (r7 i i .rfl j j rfl b).good h0 .rfl .rfl (g.base i j b),
    fun i j b => ((r7 i i .rfl j j rfl b).isBaseFrame h0 .rfl .rfl).1 (g.latS i j b),
    fun i j b => ((r7 i i .rfl j j rfl b).isBaseFrame h0 .rfl .rfl).2.1 (g.latT i j b),
    fun i j b => ((r7 i i .rfl j j rfl b).isBaseFrame h0 .rfl .rfl).2.2 (g.Pg i j b), fun i j b => ?_, fun i j b t ht => ?_,
    fun i j b t ht ha => ?_⟩
  · obtain ⟨x, h3, h4⟩ := he i i .rfl b x'
    exact (congrArg (e i b) (eq_of_heq h3).symm).trans ((g.e_LL0 i b x).trans h4)
  · have t := (r7 i i .rfl j j rfl b).de
    rw [g.delta i j b] at t
    exact TwistRel.eq ⟨t.1.symm, t.2.symm, t.3.symm⟩
  · exact (r7 i i .rfl j j rfl b).isWeil h0 .rfl .rfl .rfl .rfl
      (g.weil i j b ⟨t.Q, t.chi, t.res⟩ (TwistRel.good h0.symm ⟨.rfl, .rfl, .rfl⟩ ht))
  · exact (r7 i i .rfl j j rfl b).isClassSystem h0 .rfl .rfl (t := ⟨t.Q, t.chi, t.res⟩) ⟨.rfl, .rfl, .rfl⟩
      (r9 i i .rfl j j rfl b _ t ⟨.rfl, .rfl, .rfl⟩) (r10 i i .rfl j j rfl b _ t ⟨.rfl, .rfl, .rfl⟩)
      (g.classes i j b ⟨t.Q, t.chi, t.res⟩ (TwistRel.good h0.symm ⟨.rfl, .rfl, .rfl⟩ ht)
        ((r7 i i .rfl j j rfl b).adm h0 .rfl .rfl .rfl ha))

theorem val_move {T T' : Type} {n n' : ℕ} (hT : T = T') (hn : n = n') {a : T → GL (Fin n) ℂ} {a' : T' → GL (Fin n') ℂ}
    {c : T → Matrix (Fin n) (Fin n) ℂ} {c' : T' → Matrix (Fin n') (Fin n') ℂ} (ha : HEq a a') (hc : HEq c c')
    (g : ∀ τ, (a τ).val = c τ) (τ : T') : (a' τ).val = c' τ := by
  subst hT hn ha hc
  exact g τ

theorem mem_move {R R' : Ranks} {H : Host R} {H' : Host R'} (hR : R = R') (hH : HEq H H') {T T' : Type} (hT : T = T')
    {p : T → Finset (Pl H.E)} {p' : T' → Finset (Pl H'.E)} {c : T → Set (Pl H.E)} {c' : T' → Set (Pl H'.E)} (hp : HEq p p')
    (hc : HEq c c') {i : T} {i' : T'} (hi : HEq i i') {P : Pl H.E} {P' : Pl H'.E} (hP : HEq P P') (g : P ∈ p i → P ∈ c i) :
    P' ∈ p' i' → P' ∈ c' i' := by
  subst hR; subst hH; subst hT hp hc hi hP
  exact g

theorem grp_move {R R' : Ranks} {H : Host R} {H' : Host R'} {L L' : Fin 2 → Type} (hR : R = R') (hH : HEq H H') (hL : L = L')
    {r r' : ℕ} (e : r = R.r) (e' : r' = R'.r) {A B : Finset (Pl H.E)} {A' B' : Finset (Pl H'.E)} (hA : HEq A A') (hB : HEq B B')
    {u : (∀ kv : (Σ k : Fin 2, L k), GL (Fin R.r) (ZMod (H.g kv.1))) ≃* G0 A r}
    {u' : (∀ kv : (Σ k : Fin 2, L' k), GL (Fin R'.r) (ZMod (H'.g kv.1))) ≃* G0 A' r'} (hu : HEq u u')
    {c : G0 B R.r ≃* ∀ kv : (Σ k : Fin 2, L k), GL (Fin R.r) (ZMod (H.g kv.1))}
    {c' : G0 B' R'.r ≃* ∀ kv : (Σ k : Fin 2, L' k), GL (Fin R'.r) (ZMod (H'.g kv.1))} (hc : HEq c c')
    (g : ∀ x P (h : P ∈ A) (h' : P ∈ B) (a b : Fin r), (u x ⟨P, h⟩).val a b = (c.symm x ⟨P, h'⟩).val (Fin.cast e a) (Fin.cast e b)) :
    ∀ x P (h : P ∈ A') (h' : P ∈ B') (a b : Fin r'),
      (u' x ⟨P, h⟩).val a b = (c'.symm x ⟨P, h'⟩).val (Fin.cast e' a) (Fin.cast e' b) := by
  subst hR; subst hH; subst hL e e' hA hB hu hc
  exact g

theorem heq_app {T T' A : Type} (hT : T = T') {f : T → A} {f' : T' → A} (hf : HEq f f') {i : T} {i' : T'} (hi : HEq i i') :
    f i = f' i' := by
  subst hT hf hi
  rfl

variable {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

theorem SetupRel.good (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw} (r : SetupRel ρ ρ') (g : ρ.Good) : ρ'.Good :=
  r.good_of h.sameGeo h.gal h.set h.delta (fun _ _ hi b x => ⟨e x, h.sideEmb_heq hi b x, h.embLL0_eq x⟩) g

theorem SetupRel.realPin (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {ρ : Setup D.ntw}
    {ρ' : Setup D'.ntw} (r : SetupRel ρ ρ') (p : RealPin X.R X.cG ρ) : RealPin X'.R X'.cG ρ' := by
  have G := h.sameGeo
  have back : ∀ (i' : D'.ntw.Tw) (j' : Fin D'.R.m), ∃ i : D.ntw.Tw, ∃ j : Fin D.R.m, HEq i i' ∧ (j : ℕ) = j' :=
    fun i' j' => ⟨cast h.Tw_eq.symm i', Fin.cast (congrArg Ranks.m h.gal.R).symm j', cast_heq _ _, rfl⟩
  have chain : ∀ {A A' : Type} {a c : A} {a' c' : A'}, HEq a a' → a = c → HEq c c' → a' = c' :=
    fun h1 h2 h3 => eq_of_heq (h1.symm.trans ((heq_of_eq h2).trans h3))
  constructor
  case deltaPl =>
    intro i' t' P' h1 h2
    obtain ⟨t, P, h3, h4⟩ := m.Q i' t' P' h1 h2
    exact mem_move h.gal.R h.gal.host h.Tw_eq h.set.pD r.ch (cast_heq h.Tw_eq.symm i') h4 (p.deltaPl _ t P h3) h2
  all_goals
    intro i' j' b
    obtain ⟨i, j, hi, hj⟩ := back i' j'
    have q := r.B i i' hi j j' hj b
    obtain ⟨hV, hW, rV, rW, hp, hm⟩ := G.spaces hj
  · exact chain q.F.ψ (p.psi i j b) m.ψ
  · exact chain q.F.θ (p.inf i j b) m.θ
  · exact chain q.F.sT (p.cartT i j b) ((m.MW j j' hj).cart_onb G hW).1
  · exact val_move h.Tau rV q.F.BS (m.BV j j' hj) (p.onbS i j b)
  · exact chain q.F.BT (p.onbT i j b) ((m.MW j j' hj).cart_onb G hW).2
  · exact chain q.F.ΛS (p.latS i j b) (m.ΛV j j' hj)
  · exact chain q.F.ΛT (p.latT i j b) (m.ΛW j j' hj)
  · exact chain q.F.βS (p.frS i j b) (m.βV j j' hj)
  · exact chain q.F.βT (p.frT i j b) (m.βW j j' hj)
  · exact chain q.F.f₀ (p.vac i j b) (m.vacP j j' hj)
  · exact chain q.G.Pg (p.Pg i j b) m.Pg
  · exact grp_move h.gal.R h.gal.host (eq_of_heq h.gal.PlG) (FWT.rank_Wc j) (FWT.rank_Wc j') q.G.Pg m.Pg
      (r.eG i i' hi j j' hj b) m.cG (p.grp i j b)
  · exact chain q.mu0 (p.mu0 i j b) (hj ▸ m.mu0 j)
  · exact chain q.eta (p.eta i j b) m.eta
  · exact G.chrEq q.de.chi (heq_app h.Tw_eq h.set.l hi ▸ m.delAt _) (p.delta i j b)
  · exact congrFun (chain q.w.ap (funext (p.ap i j b)) hp)
  · exact congrFun (chain q.w.am (funext (p.am i j b)) hm)

theorem BaseRel.sameBase {S T : HSp D} {S' T' : HSp D'} {B : Base S T} {B' : Base S' T'} (r : BaseRel B B') : SameBase B B' :=
  ⟨r.F.1, r.F.2, r.F.3, r.F.4, r.F.5, r.F.6, r.F.7, r.F.8, r.F.9, r.F.10, r.G.1, r.G.2, r.G.3, ⟨r.de.1, r.de.2, r.de.3⟩,
    r.w.1, r.w.2, r.w.3, r.w.4, r.w.5, r.w.6, r.mu0, r.eta⟩

theorem SameBase.baseRel {S T : HSp D} {S' T' : HSp D'} {B : Base S T} {B' : Base S' T'} (r : SameBase B B') : BaseRel B B' :=
  ⟨⟨r.ψ, r.θ, r.sT, r.BS, r.BT, r.ΛS, r.ΛT, r.βS, r.βT, r.f₀⟩, ⟨r.Pg, r.P, r.mu⟩, ⟨r.de.1, r.de.2, r.de.3⟩,
    ⟨r.p, r.q, r.ap, r.am, r.c, r.lam⟩, r.mu0, r.eta⟩

theorem setupRel_iff_sameData {ρ : Setup D.ntw} {ρ' : Setup D'.ntw} : SetupRel ρ ρ' ↔ SameData ρ ρ' :=
  ⟨fun r => ⟨r.rc.1, r.rc.2, r.ch, r.bad, r.e, r.ek, fun i i' hi j j' hj b => (r.B i i' hi j j' hj b).sameBase, r.om,
      fun i i' hi j j' hj b t t' ht => ⟨r.Cl i i' hi j j' hj b t t' ⟨ht.1, ht.2, ht.3⟩, r.rep i i' hi j j' hj b t t' ⟨ht.1, ht.2, ht.3⟩⟩,
      r.β, r.eG⟩,
    fun r => ⟨⟨r.κ, r.art⟩, r.ch, r.bad, r.e, r.ek, fun i i' hi j j' hj b => (r.B i i' hi j j' hj b).baseRel, r.om,
      fun i i' hi j j' hj b t t' ht => (r.Cl i i' hi j j' hj b t t' ⟨ht.1, ht.2, ht.3⟩).1,
      fun i i' hi j j' hj b t t' ht => (r.Cl i i' hi j j' hj b t t' ⟨ht.1, ht.2, ht.3⟩).2, r.β, r.eG⟩⟩

theorem setup_move_data : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) (ρ : Setup D.ntw), ρ.Good → RealPin X.R X.cG ρ →
    ∃ ρ' : Setup D'.ntw, SameData ρ ρ' ∧ ρ'.Good ∧ RealPin X'.R X'.cG ρ' := by
  intro D D' ι e h X X' m ρ g p
  obtain ⟨ρ', r⟩ := exists_setupRel h.sameGeo h.gal h.set ρ
  exact ⟨ρ', setupRel_iff_sameData.1 r, r.good h g, r.realPin h m p⟩

end GlobalTheory.TwInputs.Move

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenExport
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TripInhab

open GlobalTheory.Triple GlobalTheory.EigTie
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf GalE)
open GlobalTheory.TwistAbove (twGL)

theorem isInv_twGL_iff {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K)
    (W : Submodule K (Fin a → K)) : IsInv (twGL χ r) W ↔ IsInv r W := by
  constructor
  · intro h g v hv
    have := W.smul_mem (((χ g)⁻¹ : Kˣ) : K) (h g v hv)
    rwa [GlobalTheory.TwistAbove.twGL_val, Matrix.smul_mulVec, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul] at this
  · intro h g v hv
    rw [GlobalTheory.TwistAbove.twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem isSSRep_twGL {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K)
    (h : IsSSRep r) : IsSSRep (twGL χ r) := fun W hW =>
  let ⟨W', h1, h2⟩ := h W ((isInv_twGL_iff χ r W).1 hW)
  ⟨W', (isInv_twGL_iff χ r W').2 h1, h2⟩

variable {D : D7} {C : CharFrame D} {art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om}

theorem isRepOf_twist (ha : GlobalTheory.HeckeGal.IsGlobalArtin art) (hCS : CharSide D C) {i : D.ntw.Tw} {b : Bool}
    (ρ : Reading D.ntw i b) {π : D.naut.CG D.R.r} {r : GalE D →* GL (Fin D.R.r) (Qbar (D.ntw.l i))}
    (hr : IsGaloisRepOf D π (D.ntw.l i) ρ.ι r) {ν : GalE D →* (D.ntw.O0 i)ˣ} {n : _}
    (hν : IsGal art ρ.κ ρ.ι (shiftChar C) n ν) :
    IsRepOf D (D.ntw.l i) ρ.ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) (twGL (inQ ρ.κ ν) r) := by
  refine ⟨(Units.continuous_val.comp (hν.cont (D.ntw.twistBaseCoefficientRing_isAdic i) ρ.κ_alg)).smul hr.1,
    isSSRep_twGL _ _ hr.2.1, ?_⟩
  have hfin := Formalism.L2.NR.placesOver_finite D.host.E (D.ntw.l i) (D.ntw.lPrime i).out.ne_zero
  filter_upwards [D.naut.locG_unr_ae π, hfin.compl_mem_cofinite] with w hu hwl
  intro B σ hB hσ
  have hl : w ∉ placesOver D.host.E (D.ntw.l i) := hwl
  have e1 := (hr.2.2 w hl).2.2 hu B σ hB hσ
  rw [galPol, D.naut.frobEig_tw _ _ hu, ← Matrix.charpoly_map] at e1
  have e2 := hν.frob ha (Or.inl hl) (shiftChar_unr C w) hB hσ

  have hue : D.naut.unr (D.naut.locG D.naut.etaTinv w) := (D.naut.etaTinv_def w).1
  have hfe : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {((C.eta.val w : ℂˣ) : ℂ)} := by
    rw [hCS.frob _ w ((hCS.unr_iff _ w).1 hue), hCS.etaTinv, HChar.val_inv, inv_inv]
  have hd : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ w
  have hM : ((((twGL (inQ ρ.κ ν) r σ : GL (Fin D.R.r) (Qbar (D.ntw.l i))) :
      Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.ntw.l i)))).map ρ.ι.toRingHom) =
      ρ.ι (toQ ρ.κ ((ν σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) •
        ((r σ : GL (Fin D.R.r) (Qbar (D.ntw.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.ntw.l i))).map
          ρ.ι.toRingHom := by
    ext x y
    simp [GlobalTheory.TwistAbove.twGL_val, GlobalTheory.GalChar.inQ_val]
  rw [← Matrix.charpoly_map, hM, charpoly_smul_of_prod _ _ _ e1, galPol, D.naut.locG_tw,
    D.naut.frobEig_tw _ _ (D.naut.unr_char _ _ hd hu hue), D.naut.frobEig_char _ _ _ hu hue hd hfe]
  simp only [Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun a _ => ?_)
  simp only [Function.comp_apply]
  congr 2
  rw [e2, shiftChar_val]
  have hq := normV_ne_zero (D := D) w
  have h0 := (C.eta.val w).ne_zero
  have e3 : ((D.R.nV : ℕ) : ℝ) = (D.R.r : ℝ) + (D.R.t : ℝ) := by
    rw [show D.R.nV = D.R.r + D.R.t from rfl]; push_cast; ring
  have e4 : ((normV w : ℕ) : ℂ) ^ ((((1 - (D.R.nV : ℝ)) / 2 : ℝ)) : ℂ) =
      ((normV w : ℕ) : ℂ) ^ ((((1 - (D.R.r : ℝ)) / 2 : ℝ)) : ℂ) *
        (((normV w : ℕ) : ℂ) ^ ((((D.R.t : ℝ) / 2 : ℝ)) : ℂ))⁻¹ := by
    rw [← Complex.cpow_neg, ← Complex.cpow_add _ _ hq, e3]
    congr 1
    push_cast
    ring
  rw [e4, mul_inv, inv_inv]
  ring

end GlobalTheory.TripInhab

namespace GlobalTheory.TripInhab

open GlobalTheory.Triple GlobalTheory.EigTie
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf GalE)
open GlobalTheory.TwistAbove (twGL)

theorem isTriple_of_sideB : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ Sb : Finset (PlE D.host), (∀ i, Sb ⊆ D.ntw.S0 i) → (∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm) → ChiTOk D cf → GrpSide D → CharSide D cf → ValLL0 D cf → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → EigTrue D cf Rw Sb eig → EigOcc D S θ hL Sb eig → RowParam D Rw → GlobalTheory.EigTie.ResTied D Rw → GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GaloisReps D → D.nexp.sig_all → GlobalTheory.Triple.IsTriple D := by
  intro hCheb hArt D cf Rw low Pq S hL eig θ Bs Sb hSb hks hT hG hCS hV hroot hstar hET hEO hRP hRT hGR hall
  obtain ⟨art, ha⟩ := hArt D.host.E D.nd.Om
  refine ⟨cf, art, ha, fun i hi b => ?_,
    fun i _ s => GlobalTheory.T.twistTriple_eigenvector_in_good_part D cf Rw low Pq S hL eig θ Bs Sb hSb hks hEO i s, hall⟩
  obtain ⟨ρ, w, red, hind, hres⟩ := hRT.exists_reading hstar hi b
  have hc : IsChars cf art ρ := GlobalTheory.T.firstTwistCharacters_eq_ladic_characters_allReadings hCheb hArt D cf Rw low Pq S hL eig θ Bs hT hG hCS hV hroot art ha i b ρ
  refine ⟨ρ, hc, fun s hs => ?_⟩
  subst hs
  obtain ⟨hocc, hgood, hspec⟩ := Bs.rhoS i s
  obtain ⟨π, hpar⟩ := hRP _ (D.ntw.jS_range i s).1 (D.ntw.jS_range i s).2 _ hocc hgood
  obtain ⟨r, hr⟩ := hGR π hpar.1.csd hpar.1.ralg (D.ntw.l i) ρ.ι
  obtain ⟨ν, n, hν⟩ := exists_shift ha hV ρ
  have hR1 := hspec π hpar.1.csd hpar.1.ralg hpar.2 ρ.κ ρ.ι ρ.κ_alg (fun x => ρ.read x)
  have hR2 := isRepOf_twist ha hCS ρ hr hν
  obtain ⟨A, hA⟩ := GlobalTheory.HeightCounting.FitRho.conj_of_isRepOf D ρ.ι _ _ (GlobalTheory.ChebSplitDense.chebSplit_nd hCheb D) _ _ hR1 hR2
  have hhk := GlobalTheory.TwInputs.HEig.hEig_eq_heckeVal D cf Rw low Pq S hL eig θ Bs Sb hSb hET i s ρ π hpar
  refine isTripleAt_of_conj hgood hocc hpar.1 hr ⟨n, hν⟩ A (fun g => ?_) hhk hind
    (hres.2.2 _ π r hgood ⟨_, (D.ntw.jS_range i s).1, (D.ntw.jS_range i s).2, hocc⟩ hpar hr)
  have := congrArg (fun M : GL (Fin D.R.r) (Qbar (D.ntw.l i)) => (M : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.ntw.l i)))) (hA g)
  simp only [Units.val_mul, GlobalTheory.TwistAbove.twGL_val, Matrix.mul_smul, Matrix.smul_mul] at this
  rw [Units.val_mul, Units.val_mul]
  exact this

end GlobalTheory.TripInhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanFiniteTranslatesVacuumThetaFockVacua
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

theorem map_infPart_of_nsmul {V W : HSp D} {y : WO V W} {M : ℕ} (hM : M ≠ 0) (h : (M • y).map (infPart D) = 0) :
    y.map (infPart D) = 0 := by
  ext i j
  have h1 := congrFun (congrFun h i) j
  rw [Matrix.map_apply, Matrix.smul_apply, map_nsmul, ← Nat.cast_smul_eq_nsmul D.host.F] at h1
  exact (smul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hM)

theorem map_infPart_of_mem_latO {V W : HSp D} {LV : Set (Fin V.rank → D.host.E)} {LW : Set (Fin W.rank → D.host.E)}
    {u : WO V W} (hu : u ∈ latO V W LV LW fun _ => True) : u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  unfold latO at hu
  refine AddSubgroup.closure_induction (p := fun u _ => infPart D (u i j) = 0) ?_ ?_ ?_ ?_ hu
  · rintro w ⟨α, -, -, a, -, s, -, t, -, rfl⟩
    rw [Matrix.of_apply]
    exact (show infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * V.gram k j)) =
      (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * V.gram k j) from rfl).trans (TensorProduct.zero_tmul _ _)
  · simp
  · intro x y _ _ hx hy; rw [Matrix.add_apply, RingHom.map_add, hx, hy, add_zero]
  · intro x _ hx; rw [Matrix.neg_apply, RingHom.map_neg, hx, neg_zero]

theorem trSp_theta_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ →
    ∀ (e : AE D) (M : ℕ) (O₁ : Subring ℂ), M ≠ 0 → ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O₁,
      IsThetaFunO ψ V W f ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (sW τ)) f := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hv e M O₁ hM f hf
  have hvac : IsVacO ψ θ V W (fun _ => 1) sW (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f₀ :=
    hv.2.2.2.2.2.2.2.2
  let Sp : Submodule ℂ (WO V W → ℂ) :=
    Submodule.span ℂ (Set.range fun a : {a : WO V W // a.map (infPart D) = 0} => heisO ψ V W a f₀)
  have hle : trSp ψ V W ΛV ΛW f₀ e M O₁ ≤ Sp.restrictScalars O₁ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, -, hy, rfl⟩
    exact Submodule.subset_span ⟨⟨y, map_infPart_of_nsmul hM (map_infPart_of_mem_latO hy)⟩, rfl⟩
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hle hf)
  rw [← hc]
  exact ⟨GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ V W hvac.1.1 f₀ hvac.2.theta _ c.support (fun a => a.1) c
      fun a _ => a.2,
    fun τ => GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ V W hvac.1.1 hvac.2.inf f₀ hvac.2.theta τ _ (hvac.2.fock τ) _
      c.support (fun a => a.1) c fun a _ => a.2⟩

end GlobalTheory.LevelSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLocalGenerationInertPlaceOffLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_local_generation_inertPlace_offLevel : GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∈ Sb → (∀ ε, IsPlaceIdem D v ε → ∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0) → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ¬ GlobalTheory.DownLift.GenFinite.Over PP v) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeIn R i t Sb f → GlobalTheory.DownLift.GenFinite.CleanIn R i t Sb f → GlobalTheory.DownLift.GenFinite.LikeOff R i t Sb f → f ∈ Submodule.span ℂ (GlobalTheory.DownLift.GenFinite.StepGen R i t (GlobalTheory.DownLift.GenFinite.dropPl Sb v)) := by
  first | exact @GlobalTheory.DownLift.GenFinite.Inert.step_inert | exact GlobalTheory.DownLift.GenFinite.Inert.step_inert | (intros; apply GlobalTheory.DownLift.GenFinite.Inert.step_inert <;> assumption)
end

