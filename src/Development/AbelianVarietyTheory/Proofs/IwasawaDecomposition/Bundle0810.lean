import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0791
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0779
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0789
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0782
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0793
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0783
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0800
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0785
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0756
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0778
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0801
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0753
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0760
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0766
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0796
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0769
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0767
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0754
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0761
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0717
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0750
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0781
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0797
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceOfAdmissibleTwist
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.XUni

theorem levelUni_export : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ kk u (s : SplitPlace (Dof x).host.E), s.w = (Dof x).naut.plGw kk u → ∃ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield (Dof x).host.E)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield (Dof x).host.E))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt (eta (D := Dof x) (cfOf x) w.I.xi v j) s ξ ∧ ∀ e, SideRead i b (T.k v) e → NG.LevelUni (cell (D := Dof x) l.b.Bs.exp b hA j).J (cx e (cell (D := Dof x) l.b.Bs.exp b hA j).χ) s (Dof x).R.r ψ₀ ξ := by
  intro hP hL
  refine StepW.of_all fun K B f T w hK hF _ P x l v i b ψ hA j htw hl hok kk u s hs => ?_
  obtain ⟨τ', hτ'⟩ := l.b.tau
  let kv0 : Σ k : Fin 2, (Dof x).nd.PlG k := ⟨kk, u⟩
  have hsw : ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).w = s.w := by
    rw [(cell (D := Dof x) l.b.Bs.exp b hA j).sp_w _ (Or.inr (Or.inr ⟨kv0, rfl⟩)), hs]
  obtain rfl := GlobalTheory.T.splitPlace_eq_of_cmFieldPlace_eq _ _ _ hsw
  have hg : (((Dof x).host.g kk : ℕ) : 𝓞 (Dof x).host.E) ∈
      ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).w.asIdeal := by
    rw [hsw, hs]; exact (Dof x).naut.plGw_over kk u
  have hoffkv : ∀ kv, kv ≠ kv0 → ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv)).v ≠
      ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).v := fun kv hne heq =>
    hne (GlobalTheory.PlaceInj.splitPlace_v_injective (Dof x)
      (fun k v => (cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) ⟨k, v⟩))
      (fun k v => (cell (D := Dof x) l.b.Bs.exp b hA j).sp_w _ (Or.inr (Or.inr ⟨⟨k, v⟩, rfl⟩))) heq)
  have hoffQ : ∀ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v ≠
      ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).v := fun P' hP' heq => by
    have h1 := GlobalTheory.T.splitPlaces_same_realPlace_natCast_mem _ _ _ _ heq.symm hg
    rw [(cell (D := Dof x) l.b.Bs.exp b hA j).sp_w P' (Or.inl hP')] at h1
    exact (hA.2.1 P' ((cell (D := Dof x) l.b.Bs.exp b hA j).QP_sub hP')).2 kk h1
  have hoffD : ∀ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v ≠
      ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).v := fun P' hP' heq => by
    have h1 := GlobalTheory.T.splitPlaces_same_realPlace_natCast_mem _ _ _ _ heq.symm hg
    rw [(cell (D := Dof x) l.b.Bs.exp b hA j).sp_w P' (Or.inr (Or.inl hP'))] at h1
    exact GlobalTheory.T.generator_not_mem_twist_place _ _ _ kk ((cell (D := Dof x) l.b.Bs.exp b hA j).DP_sub hP') h1
  haveI : Fact ((Dof x).host.g kv0.1).Prime := ⟨(Dof x).host.g_prime kk⟩
  let φ : AddChar (ZMod ((Dof x).host.g kv0.1)) ℂ :=
    { toFun := fun y => embLL0 (Dof x) ((l.rat.In.θ kv0.1 (Multiplicative.ofAdd (NX.xiRed (Dof x) kv0 * y)) : (↥(Dof x).LL0)ˣ) : ↥(Dof x).LL0)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a c => by rw [mul_add, ofAdd_add, map_mul, Units.val_mul, map_mul] }
  have hφ : 2 ≤ (Dof x).R.r → φ ≠ 1 := fun hr h1 => by
    have e1 := congrArg (fun χ : AddChar (ZMod ((Dof x).host.g kv0.1)) ℂ => χ 1) h1
    have hne := GlobalTheory.T.rationalDatum_characters_ne_one_at_fixedElement_residues _ _ _ _ _ _ _ _ _ l.b.Bs hr i kv0
    apply hne
    simp only [φ, AddChar.coe_mk, AddChar.one_apply, mul_one] at e1
    exact Units.ext ((embLL0 (Dof x)).injective (by rw [e1, Units.val_one, map_one]))
  have hex := GlobalTheory.T.exists_nontrivial_addChar_zmod_eq_of_ne_one ((Dof x).host.g kv0.1) (2 ≤ (Dof x).R.r) φ hφ
  let ψ' := hex.choose
  have hψ'1 : ψ' ≠ 1 := hex.choose_spec.1
  have hψ'φ : 2 ≤ (Dof x).R.r → ψ' = φ := hex.choose_spec.2
  have hex0 := GlobalTheory.T.exists_addChar_completion_of_residue_addChar (maximalRealSubfield (Dof x).host.E)
    ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).v ((Dof x).host.g kv0.1)
    ((cell (D := Dof x) l.b.Bs.exp b hA j).redG kv0) ψ' hψ'1
  let ψ₀ := hex0.choose
  have hψ₀m := hex0.choose_spec.1
  have hψ₀n := hex0.choose_spec.2.1
  have hψ₀r := hex0.choose_spec.2.2
  have hunr : (w.I.xi ((Dof x).what₂.muTw v)).UnrAt ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).w := by
    have e2 : w.I.xi ((Dof x).what₂.muTw v) = T.xiTw f v := P.q.mu.tw v
    rw [e2]
    refine GlobalTheory.T.twistedTuple_finiteOrderPart_unramified_at_typePrimes B f T v _ kk hg fun hQ => ?_
    rw [← Model.qOf_eq (P := P) v] at hQ
    exact (hA.2.1 _ hQ).2 kk hg
  have hexξ := GlobalTheory.T.compAt_baseCharacter_mul_unramified_eq_typeCharacter hP.what₂.art _ _ _ _ _ _ _ _ _ l.b.Bs l.a.val τ' hτ' j kv0 _ hs
    _ hunr ((cell (D := Dof x) l.b.Bs.exp b hA j).redG kv0)
  let ξ := hexξ.choose
  have hξc := hexξ.choose_spec.1
  have hξv := hexξ.choose_spec.2
  refine ⟨ψ₀, ξ, ⟨hψ₀m, hψ₀n⟩, hξc, fun e he => ⟨fun κ hκ => GlobalTheory.T.mem_level_iff_unipotent_at_typePlace _ _ _ _ _ _ _ _ _ _ _ _ kv0 hoffkv hoffQ hoffD κ hκ, ?_⟩⟩
  intro κ h hκ uu huu
  have hc := GlobalTheory.T.levelCharacter_eq_localFactor_at_typePlace _ _ _ _ _ _ _ _ _ _ _ (cell (D := Dof x) l.b.Bs.exp b hA j) kv0 hoffkv hoffQ hoffD κ h hκ
  have hU := (GlobalTheory.T.mem_level_iff_unipotent_at_typePlace _ _ _ _ _ _ _ _ _ _ _ (cell (D := Dof x) l.b.Bs.exp b hA j) kv0 hoffkv hoffQ hoffD κ hκ).1 h
  have hr := GlobalTheory.T.complex_typePlaceCharacter_eq_superdiag_addChar_mul_lowerDet _ l.b.Bs.exp i _ b kv0 _ _ l.rat.In.θ (fun u hu hu' => l.b.Bs.psiU i b u hu hu') _ (τ' (j.1 + 1) kv0)
    (fun y => hτ' i (j.1 + 1) b kv0 y (Nat.le_add_left 1 j.1) j.2) e he ψ₀ (fun hr y => (hψ₀r y).trans (congrArg (fun χ : AddChar (ZMod ((Dof x).host.g kv0.1)) ℂ => χ ((cell (D := Dof x) l.b.Bs.exp b hA j).redG kv0 y)) (hψ'φ hr))) ξ hξv _ hU uu huu
  exact (cx_apply e _ ⟨κ, h⟩).trans ((congrArg e hc).trans hr)

end GlobalTheory.XUni

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionEstimateOffCentreCell
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarKey.OffCell

theorem lin_eq_sum {X : Type} [AddCommGroup X] {n : ℕ} {u : Fin n → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X}
    {t : Fin n → ℝ} (hsum : toReal β = ∑ i, t i • toReal (u i)) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) :
    (ℓ β : ℝ) = ∑ i, t i * ℓ (u i) := by
  have h1 : ∑ i : Fin (n + 1), (Fin.cons (-1) t : Fin (n + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β u : Fin (n + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    simp [Fin.sum_univ_succ, hsum]
  have h2 := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h1
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h2
  simp at h2
  linarith

theorem inRCone_of_sum {X : Type} [AddCommGroup X] {n m : ℕ} {u : Fin n → LinearMap.BilinForm ℤ X}
    {γ : Fin m → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X} {t : Fin n → ℝ} (ht : ∀ i, 0 ≤ t i)
    (hsum : toReal β = ∑ i, t i • toReal (u i)) (h : ∀ i, t i ≠ 0 → InRCone γ (u i)) : InRCone γ β := by
  have h' : ∀ i, ∃ c : Fin m → ℝ, (∀ j, 0 ≤ c j) ∧ t i • toReal (u i) = ∑ j, c j • toReal (γ j) := fun i => by
    by_cases h0 : t i = 0
    · exact ⟨0, fun _ => le_rfl, by simp [h0]⟩
    · obtain ⟨c, hc, e⟩ := h i h0
      refine ⟨fun j => t i * c j, fun j => mul_nonneg (ht i) (hc j), ?_⟩
      rw [e, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
  choose c hc e using h'
  refine ⟨fun j => ∑ i, c i j, fun j => Finset.sum_nonneg fun i _ => hc i j, ?_⟩
  rw [hsum, Finset.sum_congr rfl fun i _ => e i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_smul]

theorem inRCone_of_nsmul {X : Type} [AddCommGroup X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} {k : ℕ} {c : Fin m → ℕ} (hk : 0 < k) (e : k • β = ∑ i, c i • γ i) : InRCone γ β := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨fun i => c i / k, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have h1 := congrArg (fun B : LinearMap.BilinForm ℤ X => ((B a b : ℤ) : ℝ)) e
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at h1
  push_cast at h1
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply mul_left_cancel₀ hk'.ne'
  rw [h1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by field_simp

theorem arith {K N C b h₀ f ps h l p : ℝ} (hN : 0 ≤ N) (hC : 0 ≤ C) (hb : 0 ≤ b) (hh₀ : 1 ≤ h₀) (hf : 1 ≤ f)
    (hfe : f = l - N * p) (hp : p ≤ b) (hps : ps ≤ 1) (hh : -h ≤ C * l) (hK : N + N * C + N ^ 2 * C * b + 1 ≤ K) :
    N * h₀ * ps - N * h < K * h₀ * (l - N * p) := by
  rw [← hfe]
  have hl : l = f + N * p := by linarith
  have hhf : 1 ≤ h₀ * f := by nlinarith
  have a1 : (N + N * C + N ^ 2 * C * b + 1) * (h₀ * f) ≤ K * (h₀ * f) := by gcongr
  have a2 : N * h₀ * ps ≤ N * (h₀ * f) := by
    rw [mul_assoc]; gcongr; linarith
  have a3 : N * C * f ≤ N * C * (h₀ * f) := by
    gcongr; nlinarith
  have a4 : N ^ 2 * C * b ≤ N ^ 2 * C * b * (h₀ * f) := le_mul_of_one_le_right (by positivity) hhf
  have a5 : N * (-h) ≤ N * (C * l) := by gcongr
  have a6 : N ^ 2 * C * p ≤ N ^ 2 * C * b := by gcongr
  rw [hl] at a5
  nlinarith

theorem off_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)) (b : ℕ), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms H.bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧ ψ.LinearOn u ∧ (starDepth H.bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧ (∀ i, (starDepth H.bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar ψ γ → 0 < N → StrictWith H.bar ψ N ℓ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → ∀ C : ℕ, (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → -(h β) ≤ C * ℓ β) → ∀ K : ℕ, N + N * C + N ^ 2 * C * b + 1 ≤ K → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ¬ InRCone γ β → (N : ℝ) * h β₀ * (starDepth H.bar ψ w).evalZ β - N * h β < K * h β₀ * (ℓ β - N * ψ.evalZ β) := by
  intro E _ _ _ H q ψ w b hψ hw X _ _ _ _ hX hgen m γ N ℓ hγ hN hsw β₀ hβ₀ hβ₀n hw₀ hc₀ m' s h hcut hpos C hC K hK β hβ hβn
    hoff
  have hon := (GlobalTheory.T.starDepth_le_on_centre_cell E H q ψ w hψ hw X hX m γ hγ β₀ hβ₀ hβ₀n hw₀ hc₀ m' s h hcut hpos).1
  obtain ⟨n, u, hu, hun, hlψ, hlp, hub, hu1, t, ht, hsum⟩ := hgen β hβ hβn
  have hh₀ : (1 : ℝ) ≤ h β₀ := by exact_mod_cast hpos
  have hoffu : ∀ i, ¬ InRCone γ (u i) → (N : ℝ) * h β₀ * (starDepth H.bar ψ w).evalZ (u i) - N * h (u i) <
      K * h β₀ * (ℓ (u i) - N * ψ.evalZ (u i)) := fun i hi => by
    obtain ⟨z, hz⟩ := (hψ X hX).integral (u i) (hu i) (hun i)
    have hle := hsw.2.1 (u i) (hu i) (hun i)
    have hne : (N : ℝ) * ψ.evalZ (u i) ≠ ℓ (u i) := fun e => by
      obtain ⟨k, c, hk, e'⟩ := hsw.2.2 (u i) (hu i) (hun i) e
      exact hi (inRCone_of_nsmul hk e')
    have hlt : (N : ℤ) * z < ℓ (u i) := by
      have := lt_of_le_of_ne hle hne
      rw [hz] at this
      exact_mod_cast this
    have hf : (1 : ℝ) ≤ ℓ (u i) - N * ψ.evalZ (u i) := by
      rw [hz]
      have : (1 : ℤ) ≤ ℓ (u i) - N * z := by omega
      exact_mod_cast this
    refine arith (C := C) (b := b) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hh₀ hf rfl (hub i) (hu1 i) ?_ ?_
    · exact_mod_cast hC (u i) (hu i) (hun i)
    · exact_mod_cast hK
  have hall : ∀ i, (N : ℝ) * h β₀ * (starDepth H.bar ψ w).evalZ (u i) - N * h (u i) ≤
      K * h β₀ * (ℓ (u i) - N * ψ.evalZ (u i)) := fun i => by
    by_cases hi : InRCone γ (u i)
    · rw [ell_eq_of_inRCone hγ.linear hsw hi, sub_self, mul_zero, mul_assoc, ← mul_sub]
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (sub_nonpos.2 (hon _ (hu i) (hun i) hi))
    · exact (hoffu i hi).le
  obtain ⟨i₀, hi₀, hi₀'⟩ : ∃ i, t i ≠ 0 ∧ ¬ InRCone γ (u i) := by
    by_contra hcon
    exact hoff (inRCone_of_sum ht hsum fun i hi => by_contra fun h' => hcon ⟨i, hi, h'⟩)
  have e1 : ψ.evalZ β = ∑ i, t i * ψ.evalZ (u i) := by
    rw [← evalR_toReal, hsum]; exact (linearOn_iff ψ u).1 hlψ t ht
  have e2 : (starDepth H.bar ψ w).evalZ β = ∑ i, t i * (starDepth H.bar ψ w).evalZ (u i) := by
    rw [← evalR_toReal, hsum]; exact (linearOn_iff _ u).1 hlp t ht
  have key : ∑ i, t i * ((N : ℝ) * h β₀ * (starDepth H.bar ψ w).evalZ (u i) - N * h (u i)) <
      ∑ i, t i * (K * h β₀ * (ℓ (u i) - N * ψ.evalZ (u i))) :=
    Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hall i) (ht i))
      ⟨i₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hoffu i₀ hi₀') (lt_of_le_of_ne (ht i₀) hi₀.symm)⟩
  rw [e1, e2, lin_eq_sum hsum h, lin_eq_sum hsum ℓ]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  convert key using 2 with i _ i _ <;> ring

end GlobalTheory.PolFan.StarKey.OffCell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionNewCellMultiplicityLt
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan.StarNewCell

variable {X : Type} [AddCommGroup X]

theorem inRCone_trans {m n : ℕ} {δ : Fin m → LinearMap.BilinForm ℤ X} {γ : Fin n → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} (hγ : ∀ k, InRCone δ (γ k)) (hβ : InRCone γ β) : InRCone δ β := by
  obtain ⟨c, hc, hβ⟩ := hβ
  choose a ha hγ using hγ
  refine ⟨fun i => ∑ k, c k * a k i, fun i => Finset.sum_nonneg fun k _ => mul_nonneg (hc k) (ha k i), ?_⟩
  rw [hβ]
  simp only [hγ, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

theorem val_eq (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} {c : Fin m → ℝ} (e : toReal β = ∑ i, c i • toReal (γ i)) :
    (h β : ℝ) = ∑ i, c i * (h (γ i) : ℝ) := by
  have := sum_mul_eq_of_sum_toReal_eq (j := LinearMap.id) Function.injective_id h (u := fun _ : Fin 1 => β) (w := γ)
    (a := fun _ => 1) (b := c) (by simpa using e)
  simpa using this

theorem val_nonneg (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} (h0 : ∀ i, 0 ≤ h (γ i)) (hβ : InRCone γ β) : 0 ≤ h β := by
  obtain ⟨c, hc, e⟩ := hβ
  have : (0 : ℝ) ≤ h β := by
    rw [val_eq h e]; exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (by exact_mod_cast h0 i)
  exact_mod_cast this

theorem val_zero (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} (h0 : ∀ i, h (γ i) = 0) (hβ : InRCone γ β) : h β = 0 := by
  obtain ⟨c, hc, e⟩ := hβ
  have : (h β : ℝ) = 0 := by
    rw [val_eq h e]; exact Finset.sum_eq_zero fun i _ => by rw [h0 i]; simp
  exact_mod_cast this

theorem inRCone_cons_succ {n : ℕ} (x : LinearMap.BilinForm ℤ X) (p : Fin n → LinearMap.BilinForm ℤ X) (k : Fin n) :
    InRCone (Fin.cons x p : Fin (n + 1) → LinearMap.BilinForm ℤ X) (p k) := by
  simpa using inRCone_self (Fin.cons x p : Fin (n + 1) → LinearMap.BilinForm ℤ X) k.succ

theorem inRCone_cons_zero {n : ℕ} (x : LinearMap.BilinForm ℤ X) (p : Fin n → LinearMap.BilinForm ℤ X) :
    InRCone (Fin.cons x p : Fin (n + 1) → LinearMap.BilinForm ℤ X) x := by
  simpa using inRCone_self (Fin.cons x p : Fin (n + 1) → LinearMap.BilinForm ℤ X) 0

end GlobalTheory.PolFan.StarNewCell

open GlobalTheory.PolFan.StarNewCell in

theorem GlobalTheory.PolFan.cellMult_lt_of_star_new : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    SimpLab H.bar q φ lab → IsCentreSet H.bar q φ w →
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
          ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) →
    ∀ M : ℕ, maxMult H.bar q φ ≤ M →
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell H.bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim H.bar (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) →
        ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (β₀ : LinearMap.BilinForm ℤ X) (m' : ℕ) (s : Fin m' ↪ Fin m)
          (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar φ γ → β₀ ∈ balForms H.bar X → (∀ y, 0 ≤ β₀ y y) →
          w.evalZ β₀ = 1 → InRCone γ β₀ → IsFaceCut γ s h → 0 < h β₀ →
          IsCell H.bar ψ' (Fin.cons β₀ fun j => γ (s j)) → (∀ j, InRCone (Fin.cons β₀ fun j => γ (s j)) (γ' j)) →
          cellMult H.bar (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) < M := by
  intro E _ _ _ H q φ lab w ψ' hSL hCS hcoord M hM X _ _ _ _ hX n γ' hγ' hliγ' hprimγ' m γ β₀ m' s h hγ hβ₀ hβ₀p hw
    hβ₀γ hcut hpos hτ hγ'τ
  classical

  obtain ⟨m₀, δ, hδ, hliδ, -, hγδ⟩ := hSL.2 X hX m γ hγ
  obtain ⟨δt, hδt, hliδt, hprimδt, hδδt⟩ := GlobalTheory.T.exists_rescale_primitive_linearIndependent_cell H.bar φ δ hδ hliδ
  have hγδt : ∀ k, InRCone δt (γ k) := fun k => hδδt _ (hγδ k)

  obtain ⟨h₂, h₂0, h₂γ, h₂cut⟩ := GlobalTheory.T.exists_linForm_cut_face_of_cell_in_cone H.bar φ δt γ hδt hγ hγδt
  have hcutγ : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → h β = 0 →
      InRCone (fun k => γ (s k)) β :=
    fun β _ _ hβ hβ0 => GlobalTheory.T.inRealCone_generators_of_linForm_eq_zero γ h s β hcut.1 (fun i hi => (hcut.2 i).1 hi) hβ hβ0
  have hhs : ∀ k, h (γ (s k)) = 0 := fun k => (hcut.2 (s k)).2 ⟨k, rfl⟩
  obtain ⟨h₃, h₃0, h₃γs, h₃cut⟩ := GlobalTheory.T.exists_linForm_cut_face_of_face_of_cone H.bar δt γ (fun k => γ (s k)) h₂ h hδt.mem hδt.nonneg
    (fun k => inRCone_self γ (s k)) h₂0 h₂γ h₂cut hcut.1 hhs hcutγ

  set I : Finset (Fin m₀) := Finset.univ.filter (fun i => h₃ (δt i) = 0) with hI
  set eI : Fin I.card ↪ Fin m₀ := (I.orderEmbOfFin rfl).toEmbedding with heIdef
  have heI : ∀ i, i ∈ Set.range eI ↔ h₃ (δt i) = 0 := by
    intro i
    show i ∈ Set.range (I.orderEmbOfFin rfl) ↔ _
    rw [Finset.range_orderEmbOfFin]
    simp [I]
  have hsupp : ∀ β, InRCone δt β → h₃ β = 0 → InRCone (fun k => δt (eI k)) β :=
    fun β hβ h0 => GlobalTheory.T.inRealCone_generators_of_linForm_eq_zero δt h₃ eI β h₃0 (fun i hi => (heI i).2 hi) hβ h0

  obtain ⟨c, hc0, hcβ⟩ : InRCone δt β₀ := inRCone_trans hγδt hβ₀γ
  have hclt : ∀ i, c i < 1 := hcoord X hX m₀ δt hδt hliδt hprimδt β₀ hβ₀ hβ₀p hw c hc0 hcβ
  obtain ⟨j, hcj, hjI⟩ : ∃ j, 0 < c j ∧ h₃ (δt j) ≠ 0 := by
    by_contra hno
    push_neg at hno
    have h30 : h₃ β₀ = 0 := by
      have : (h₃ β₀ : ℝ) = 0 := by
        rw [val_eq h₃ hcβ]
        refine Finset.sum_eq_zero fun i _ => ?_
        rcases (hc0 i).eq_or_lt with hi | hi
        · rw [← hi, zero_mul]
        · rw [hno i hi]; simp
      exact_mod_cast this
    have := val_zero h hhs (h₃cut β₀ hβ₀ hβ₀p ⟨c, hc0, hcβ⟩ h30)
    omega

  have hprimβ₀ : ∀ hx : β₀ ∈ balForms H.bar X, IsPrim H.bar (⟨β₀, hx⟩ : balForms H.bar X) := by
    intro hx k β' hk
    refine (hCS X hX).2.1 β₀ hβ₀ hβ₀p hw k β' ?_
    have h' : β₀ = ((k • β' : balForms H.bar X) : LinearMap.BilinForm ℤ X) := congrArg Subtype.val hk
    rw [h', Submodule.coe_smul_of_tower, natCast_zsmul]

  set δs : Fin m₀ → balForms H.bar X := fun i => ⟨δt i, hδt.mem i⟩ with hδs
  set βs : balForms H.bar X := ⟨β₀, hβ₀⟩ with hβs
  have hliδs : LinearIndependent ℤ δs := LinearIndependent.of_comp (balForms H.bar X).subtype hliδt

  set ρs : Fin (I.card + 1) → balForms H.bar X := Fin.cons βs (fun k => δs (eI k)) with hρsdef
  obtain ⟨ρ, hρ0, hρs, hρv⟩ : ∃ ρ : Fin (I.card + 1) → LinearMap.BilinForm ℤ X, ρ 0 = β₀ ∧
      (∀ k, ρ k.succ = δt (eI k)) ∧ ∀ i, ρ i = (ρs i : LinearMap.BilinForm ℤ X) :=
    ⟨fun i => (ρs i : LinearMap.BilinForm ℤ X), by simp [ρs, βs], fun k => by simp [ρs, δs], fun i => rfl⟩
  have hjeI : j ∉ Set.range eI := fun hh => hjI ((heI j).1 hh)
  have hliρ : LinearIndependent ℤ ρ := by
    have h1 := GlobalTheory.T.linearIndependent_cons_balancedForm_of_coord_ne_zero H.bar δs βs c j eI hliδs hcβ hcj.ne' hjeI
    have h2 := h1.map' (balForms H.bar X).subtype (Submodule.ker_subtype _)
    have : ρ = (balForms H.bar X).subtype ∘ ρs := funext hρv
    rw [this]; exact h2
  have hρmem : ∀ i, ρ i ∈ balForms H.bar X := fun i => by rw [hρv]; exact (ρs i).2
  have hρnn : ∀ i y, 0 ≤ ρ i y y := by
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · rw [hρ0]; exact hβ₀p
    · rw [hρs]; exact hδt.nonneg _
  have hρprim : ∀ i, IsPrim H.bar (⟨ρ i, hρmem i⟩ : balForms H.bar X) := by
    have key : ∀ (x y : LinearMap.BilinForm ℤ X) (hx : x ∈ balForms H.bar X) (hy : y ∈ balForms H.bar X), x = y →
        IsPrim H.bar (⟨y, hy⟩ : balForms H.bar X) → IsPrim H.bar (⟨x, hx⟩ : balForms H.bar X) := by
      rintro x y hx hy rfl hp; exact hp
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · exact key _ _ _ hβ₀ hρ0 (hprimβ₀ hβ₀)
    · exact key _ _ _ (hδt.mem _) (hρs k) (hprimδt _)

  have hτρ : ∀ i, InRCone ρ ((Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) i) := by
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · rw [Fin.cons_zero, ← hρ0]; exact inRCone_self ρ 0
    · rw [Fin.cons_succ]
      exact inRCone_trans (fun l => hρs l ▸ inRCone_self ρ l.succ) (hsupp _ (hγδt (s k)) (h₃γs k))
  have hρτ : ∀ i, InRCone (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) (ρ i) := by
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · rw [hρ0]; exact inRCone_cons_zero _ _
    · rw [hρs]
      exact inRCone_trans (fun l => inRCone_cons_succ β₀ (fun j => γ (s j)) l)
        (h₃cut _ (hδt.mem _) (hδt.nonneg _) (inRCone_self δt _) ((heI _).1 ⟨k, rfl⟩))

  obtain ⟨h₁, h₁0, h₁γ', h₁cut⟩ := GlobalTheory.T.exists_linForm_cut_face_of_cell_in_cone H.bar ψ' _ γ' hτ hγ' hγ'τ
  obtain ⟨s', hs', -⟩ := GlobalTheory.T.eq_subfamily_of_face_simplicialCone_primitive H.bar ρ γ' hρmem hγ'.mem h₁ hliρ hliγ' hρprim hprimγ'
    (fun k => inRCone_trans hτρ (hγ'τ k)) (fun i => val_nonneg h₁ h₁0 (hρτ i)) h₁γ'
    (fun i hi => h₁cut (ρ i) (hρmem i) (hρnn i) (hρτ i) hi)

  set J : Finset (Fin m₀) := Finset.univ.erase j with hJ
  have hJc : J.card = m₀ - 1 := by simp [J]
  set eJ : Fin (m₀ - 1) ↪ Fin m₀ := (J.orderEmbOfFin hJc).toEmbedding with heJdef
  have heJ : ∀ i, i ∈ Set.range eJ ↔ i ≠ j := by
    intro i
    show i ∈ Set.range (J.orderEmbOfFin hJc) ↔ _
    rw [Finset.range_orderEmbOfFin]
    simp [J]
  set ρ's : Fin (m₀ - 1 + 1) → balForms H.bar X := Fin.cons βs (fun k => δs (eJ k)) with hρ'sdef
  have hliρ' : LinearIndependent ℤ ρ's := GlobalTheory.T.linearIndependent_cons_balancedForm_of_coord_ne_zero H.bar δs βs c j eJ hliδs hcβ hcj.ne' (fun hh => (heJ j).1 hh rfl)
  have hmultρ' : (cellMult H.bar ρ's : ℝ) = c j * cellMult H.bar δs :=
    GlobalTheory.T.cell_multiplicity_positive_cone H.bar δs βs c j eJ hliδs hcβ hcj heJ (GlobalTheory.T.balancedFormCellMultiplicity_pos H.bar δs)
  have hrange : Set.range (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) ⊆ Set.range ρ's := by
    rintro _ ⟨k, rfl⟩
    have e := hs' k
    rcases Fin.eq_zero_or_eq_succ (s' k) with h0 | ⟨l, hl⟩
    · refine ⟨0, Subtype.ext ?_⟩
      simp [ρ's, βs]
      rw [e, h0, hρ0]
    · have hne : eI l ≠ j := fun hh => hjI (hh ▸ (heI (eI l)).1 ⟨l, rfl⟩)
      obtain ⟨r, hr⟩ := (heJ (eI l)).2 hne
      refine ⟨r.succ, Subtype.ext ?_⟩
      simp [ρ's, δs]
      rw [e, hl, hρs, hr]
  have hdvd : cellMult H.bar (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) ∣ cellMult H.bar ρ's :=
    GlobalTheory.T.natCard_torsion_quot_span_dvd_of_range_subset' (balForms H.bar X) ρ's _ hliρ' hrange
  have hle := Nat.le_of_dvd (GlobalTheory.T.balancedFormCellMultiplicity_pos H.bar ρ's) hdvd
  have hδpos := GlobalTheory.T.balancedFormCellMultiplicity_pos H.bar δs
  have hlt : (cellMult H.bar ρ's : ℝ) < cellMult H.bar δs := by
    rw [hmultρ']; exact mul_lt_of_lt_one_left (by exact_mod_cast hδpos) (hclt j)
  have hlt' : cellMult H.bar ρ's < cellMult H.bar δs := by exact_mod_cast hlt
  have hδsM : cellMult H.bar δs ≤ M := by
    have := (SmoothEnd.cellMult_le_maxMult hX hδt hliδt hprimδt).trans hM
    exact_mod_cast this
  omega
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedStateTransportHeq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeightCounting.Up

open GlobalTheory.Mem.R3.Tr

theorem restage_copy : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : LI hL x) (N : TwNew (Dof x)), ∃ (x' : St P) (l' : LI hL x'), x'.o = oTw x N ∧ HEq x'.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x.o.Z) (oTw x N).Z x.m.z.R.toRealDat.toLevCh) ∧ HEq l'.a.A.row (N.row l.a.A.row) ∧ HEq l'.Pq l.Pq ∧ HEq l'.rat.S (N.rat l.rat.S) ∧ HEq l'.rat.In.Sb l.rat.In.Sb ∧ HEq l'.rat.In.hL l.rat.In.hL ∧ HEq l'.rat.In.eig l.rat.In.eig ∧ HEq l'.rat.In.θ l.rat.In.θ := by
  intro hL K B f T w P x l N
  obtain ⟨m, hm, hc, hh⟩ := GlobalTheory.T.exists_movedData_laterStagesWithNewTwist x N
  obtain ⟨r, hp, hrep, hj, he⟩ := GlobalTheory.T.exists_normalisedReading_transported_newTwist x N m hm hc hh
  obtain ⟨l', h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.T.read_package_twist_heq hL x l N m hm hc hh r hp hrep hj he
  refine ⟨stTw x N m hc hh r hp, l', rfl, ?_, h1, h2, h3, h4, h5, h6, h7⟩
  show HEq m.z.R.toRealDat.toLevCh _
  rw [hm]
  exact (by with_unfolding_all exact ((HEq.refl (datTw x N).R.toRealDat.toLevCh) :))

end GlobalTheory.HeightCounting.Up

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedStateTransportHeqLevels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeightCounting.Up

open GlobalTheory.Mem.R3.Tr

theorem restage_copy_real : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : LI hL x) (N : TwNew (Dof x)), ∃ (x' : St P) (l' : LI hL x'), x'.o = oTw x N ∧ HEq x'.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x.o.Z) (oTw x N).Z x.m.z.R.toRealDat.toLevCh) ∧ HEq l'.a.A.row (N.row l.a.A.row) ∧ HEq l'.Pq l.Pq ∧ HEq l'.rat.S (N.rat l.rat.S) ∧ HEq l'.rat.In.Sb l.rat.In.Sb ∧ HEq l'.rat.In.hL l.rat.In.hL ∧ HEq l'.rat.In.eig l.rat.In.eig ∧ HEq l'.rat.In.θ l.rat.In.θ ∧ HEq x'.m.z.R (GlobalTheory.Mem.R3.Tr.real3 (a := x.o.Z) (oTw x N).Z (iK := x.m.z.alg) x.m.z.R) ∧ HEq x'.m.z.cG x.m.z.cG ∧ HEq x'.m.z.geo (GlobalTheory.Mem.R3.Tr.geoHalf (a := x.o.Z) (oTw x N).Z (iK := x.m.z.alg) x.m.z.geo) := by
  intro hL K B f T w P x l N
  obtain ⟨m, hm, hc, hh⟩ := GlobalTheory.T.exists_movedData_laterStagesWithNewTwist x N
  obtain ⟨r, hp, hrep, hj, he⟩ := GlobalTheory.T.exists_normalisedReading_transported_newTwist x N m hm hc hh
  obtain ⟨l', h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.T.read_package_twist_heq hL x l N m hm hc hh r hp hrep hj he
  refine ⟨stTw x N m hc hh r hp, l', rfl, ?_, h1, h2, h3, h4, h5, h6, h7, ?_, ?_, ?_⟩
  · show HEq m.z.R.toRealDat.toLevCh _
    rw [hm]
    exact (by with_unfolding_all exact ((HEq.refl (datTw x N).R.toRealDat.toLevCh) :))
  · show HEq m.z.R _
    rw [hm]
    exact (by with_unfolding_all exact ((HEq.refl (datTw x N).R) :))
  · show HEq m.z.cG _
    rw [hm]
    exact (by with_unfolding_all exact ((HEq.refl (datTw x N).cG) :))
  · show HEq m.z.geo _
    rw [hm]
    exact (by with_unfolding_all exact ((HEq.refl (datTw x N).geo) :))

end GlobalTheory.HeightCounting.Up

end
end

