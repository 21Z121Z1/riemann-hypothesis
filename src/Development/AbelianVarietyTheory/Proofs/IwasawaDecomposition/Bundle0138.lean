import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxUnramifiedSubfieldConjIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0118
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LpUnrNegOneSpec
section
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open GlobalTheory.WeilDeligne

section

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

abbrev WDAt (N : NData R H what₂) (w : PlE H) : Type :=
  WD (E := H.E) (A := N.plOm.1 w) (w := w) (N.plOm.2 w)

abbrev UnrWDFam (N : NData R H what₂) (a : ℕ) : Type :=
  {p : (∀ w, WDAt N w) × ((H.E →+* ℂ) → Multiset ℂ) //
    (∀ w, (p.1 w).unr ∧ (p.1 w).lpDim = a) ∧ ∀ τ, Multiset.card (p.2 τ) = a}

theorem lpUnr_negOne_spec (N : NData R H what₂) (w : PlE H) :
    (WD.lpUnr (N.plOm.2 w) {-1} : WDAt N w).unr ∧ (WD.lpUnr (N.plOm.2 w) {-1} : WDAt N w).frobEig = {-1} ∧
      (WD.lpUnr (N.plOm.2 w) {-1} : WDAt N w).lpDim = 1 := by
  obtain ⟨hu, he, hd⟩ := WD.lpUnr_spec (h := N.plOm.2 w) ({-1} : Multiset ℂ) (by simp)
  exact ⟨hu, he, hd.trans (Multiset.card_singleton _)⟩

def negOneWDFam (N : NData R H what₂) : UnrWDFam N 1 :=
  ⟨(fun w => WD.lpUnr (N.plOm.2 w) {-1}, fun _ => {0}),
    fun w => ⟨(lpUnr_negOne_spec N w).1, (lpUnr_negOne_spec N w).2.2⟩, fun _ => rfl⟩

theorem UnrWDFam.exists_frobEig {N : NData R H what₂} (χ : UnrWDFam N 1) (w : PlE H) :
    ∃ c, (χ.1.1 w).frobEig = {c} := by
  have hu : (χ.1.1 w).unr := (χ.2.1 w).1
  have hd : (χ.1.1 w).lpDim = 1 := (χ.2.1 w).2
  have hc : Multiset.card (χ.1.1 w).frobEig = 1 := ((WD.unramified_laws (N.plOm.2 w)).2.2.2.2.2.2.2.2.2.2.2.2.1 _ hu).trans hd
  exact Multiset.card_eq_one.mp hc

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

def nAutWD (N : NData R H what₂) (hE : IsEmpty N.Loc) (pl : ∀ k, N.PlG k → PlE H)
    (h1 : ∀ k v, pl k v ∈ placesOver H.E (H.g k)) (h2 : ∀ k, Function.Injective (pl k))
    (h3 : ∀ k v v', ¬ IsConjPl H (pl k v) (pl k v'))
    (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ) (γ : Fin 2 → PlE H → G H.E N.Om) : NAut N where
  LP := WDAt N
  lpDim := WD.lpDim
  lpZero := fun w => WD.lpZero (N.plOm.2 w)
  lpSum := WD.lpSum
  lpTw := WD.lpTw
  lpChar := WD.lpChar
  lpUnr := fun w => WD.lpUnr (N.plOm.2 w)
  mono0 := WD.mono0
  unr := WD.unr
  frobEig := WD.frobEig
  tempered := WD.tempered
  inePol := WD.inePol
  items₂ := fun k w a => haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩; WD.lab (τ k) (γ k w) a
  lpDim_zero := fun w => WD.lpDim_zero _
  lpDim_sum := WD.lpDim_sum
  lpDim_tw := WD.lpDim_tw
  lpUnr_spec := fun _ => WD.lpUnr_spec
  unr_sum := WD.unr_sum
  monomial_sum_iff := WD.monomial_sum_iff
  frobEig_sum := fun a b _ _ => WD.frobEig_lpSum a b
  unr_tw := WD.unr_tw
  monomial_twist_iff := WD.monomial_twist_iff
  frobEig_tw := WD.frobEig_tw
  frobEig_char := fun a χ c ha hχ _ => WD.frobEig_char a χ c ha hχ
  lpDim_char := WD.lpDim_char
  unr_char := fun a χ _ => WD.unr_lpChar a χ
  monomial_char_iff := WD.monomial_char_iff
  lpZero_unr := fun _ => WD.lpZero_unr
  frobEig_zero := fun _ => WD.frobEig_zero
  lpSum_zero := WD.lpSum_zero
  lpSum_comm := WD.lpSum_comm
  lpSum_assoc := WD.lpSum_assoc
  lpTw_zero := WD.lpTw_zero
  lpTw_add := WD.lpTw_add
  lpTw_sum := WD.lpTw_sum
  unr_eq_lpUnr := WD.unr_eq_lpUnr
  unr_mono0 := WD.unr_mono0
  frobEig_ne_zero := WD.frobEig_ne_zero
  frobEig_card := fun a _ => WD.card_eig a _
  tempered_unr := WD.tempered_unr
  inePol_sum := WD.inePol_sum
  inePol_tw := WD.inePol_tw
  unr_iff_ine := WD.unr_iff_ine
  inertiaCharpoly_zero := fun k _ => haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩; WD.lab_lpZero _ _
  inertiaCharpoly_add := fun k _ a b => haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩; WD.lab_lpSum _ _ a b
  CG := UnrWDFam N
  csd := fun π => ∀ w w', IsConjPl H w w' → (π.1.1 w').frobEig = (π.1.1 w).frobEig.map (·⁻¹)
  ralg := fun {a} π => ∀ τ, (π.1.2 τ).Nodup ∧ ∀ z ∈ π.1.2 τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2
  locG := fun π w => π.1.1 w
  locG_dim := fun π w => (π.2.1 w).2
  locG_unr_ae := fun π => Filter.Eventually.of_forall fun w => (π.2.1 w).1
  tw := fun π χ => ⟨(fun w => (π.1.1 w).lpChar (χ.1.1 w), fun τ => (π.1.2 τ).map (· + (χ.1.2 τ).sum)),
    fun w => ⟨WD.unr_lpChar _ _ (π.2.1 w).1 (χ.2.1 w).1, (WD.lpDim_char _ _ (χ.2.1 w).2).trans (π.2.1 w).2⟩,
    fun τ => (Multiset.card_map _ _).trans (π.2.2 τ)⟩
  locG_tw := fun _ _ _ => rfl
  infG := fun π τ => π.1.2 τ
  infG_card := fun π τ => π.2.2 τ
  ralg_def := fun _ => Iff.rfl
  infG_tw := fun π χ τ s h => by
    show (π.1.2 τ).map (· + (χ.1.2 τ).sum) = _
    rw [show χ.1.2 τ = {s} from h, Multiset.sum_singleton]
  csd_tw := fun π χ hχ hπ w w' h => by
    obtain ⟨c, hc⟩ := χ.exists_frobEig w
    have hc' := hχ w w' h
    rw [hc, Multiset.map_singleton] at hc'
    show ((π.1.1 w').lpChar (χ.1.1 w')).frobEig = ((π.1.1 w).lpChar (χ.1.1 w)).frobEig.map (·⁻¹)
    rw [WD.frobEig_char _ _ _ (π.2.1 w').1 (χ.2.1 w').1 hc', WD.frobEig_char _ _ _ (π.2.1 w).1 (χ.2.1 w).1 hc,
      hπ w w' h, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun x _ => (mul_inv _ _).symm
  csd_unr := fun π w w' h hc _ => ⟨(π.2.1 w').1, h w w' hc⟩
  etaT := negOneWDFam N
  etaTinv := negOneWDFam N
  etaT_unr := fun w => (lpUnr_negOne_spec N w).1
  etaT_inert := fun w _ => (lpUnr_negOne_spec N w).2.1
  etaTinv_def := fun w => ⟨(lpUnr_negOne_spec N w).1, by
    show (WD.lpUnr (N.plOm.2 w) {-1} : WDAt N w).frobEig = (WD.lpUnr (N.plOm.2 w) {-1} : WDAt N w).frobEig.map (·⁻¹)
    rw [(lpUnr_negOne_spec N w).2.1]
    simp⟩
  etaT_split := fun w w' _ _ a b ha hb => by
    have ha' : (-1 : ℂ) = a := Multiset.singleton_inj.1 ((lpUnr_negOne_spec N w).2.1.symm.trans ha)
    have hb' : (-1 : ℂ) = b := Multiset.singleton_inj.1 ((lpUnr_negOne_spec N w').2.1.symm.trans hb)
    rw [← ha', ← hb']
    norm_num
  plGw := pl
  plGw_over := h1
  plGw_inj := h2
  plGw_nconj := h3
  iotaQ := fun i => hE.elim i
  iotaQC := fun i => hE.elim i
  iota_LL := fun i => hE.elim i
  iotaQ_alg := fun i => hE.elim i
  muC := fun i => hE.elim i
  muC_csd := fun i => hE.elim i
  AV := fun i => hE.elim i
  finAV := fun i => hE.elim i
  ptV := fun i => hE.elim i
  typeV := fun i => hE.elim i
  typeV_ne := fun i => hE.elim i
  typeV_indep := fun i => hE.elim i
  typeV_top := fun i => hE.elim i
  pt_surj := fun i => hE.elim i
  eig_dim := fun i => hE.elim i
  locV := fun i => hE.elim i
  satV := fun i => hE.elim i
  locV_unr := fun i => hE.elim i
  pt_loc := fun i => hE.elim i
  infWt := fun i => hE.elim i
  locW := fun i => hE.elim i
  satW := fun i => hE.elim i
  lab_loc := fun i => hE.elim i
  wdOf := fun i => hE.elim i
  wdOf_dim := fun i => hE.elim i
  wdOf_unr := fun i => hE.elim i
  wdOf_frob := fun i => hE.elim i
  wdOf_ine := fun i => hE.elim i
  wdOf_mono0 := fun i => hE.elim i
  IsCrysW := fun i => hE.elim i
  IsPotCrysW := fun i => hE.elim i
  IsdRW := fun i => hE.elim i
  jumpsW := fun i => hE.elim i
  wdOf_unrL := fun i => hE.elim i
  wdOf_mono0L := fun i => hE.elim i
  jumpsInf := fun i => hE.elim i
  locAutHodgeTateWeightsLevelZero := fun i => hE.elim i
  jumpsInf_def := fun i => hE.elim i
  locAut_hodgeTateWeightsLevelZero_def := fun i => hE.elim i
  chi_mu := fun i => hE.elim i
  kFbar := fun i => hE.elim i

def wdTieWD (N : NData R H what₂) (hE : IsEmpty N.Loc) (pl : ∀ k, N.PlG k → PlE H)
    (h1 : ∀ k v, pl k v ∈ placesOver H.E (H.g k)) (h2 : ∀ k, Function.Injective (pl k))
    (h3 : ∀ k v v', ¬ IsConjPl H (pl k v) (pl k v'))
    (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ) (γ : Fin 2 → PlE H → G H.E N.Om) :
    GlobalTheory.RowTie.WDTie N (nAutWD N hE pl h1 h2 h3 τ γ) :=
  ⟨fun _ => Equiv.refl _, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ _ => Iff.rfl, fun _ _ _ _ => rfl⟩

theorem exists_nAut_wdTie (N : NData R H what₂) (hE : IsEmpty N.Loc) (pl : ∀ k, N.PlG k → PlE H)
    (h1 : ∀ k v, pl k v ∈ placesOver H.E (H.g k)) (h2 : ∀ k, Function.Injective (pl k))
    (h3 : ∀ k v v', ¬ IsConjPl H (pl k v) (pl k v'))
    (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ) (t : ∀ k, N.PlG k → G H.E N.Om) :
    ∃ (A : NAut N) (T : GlobalTheory.RowTie.WDTie N A), A.plGw = pl ∧ ∀ k v (a : A.LP (A.plGw k v)),
      haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
      A.items₂ k (A.plGw k v) a = WD.lab (τ k) (t k v) (T.e _ a) := by
  classical
  let γ : Fin 2 → PlE H → G H.E N.Om := fun k => Function.extend (pl k) (t k) fun _ => 1
  refine ⟨nAutWD N hE pl h1 h2 h3 τ γ, wdTieWD N hE pl h1 h2 h3 τ γ, rfl, fun k v a => ?_⟩
  have hγ : γ k (pl k v) = t k v := (h2 k).extend_apply _ _ _
  have : Fact (H.g k).Prime := ⟨H.g_prime k⟩
  show WD.lab (τ k) (γ k (pl k v)) a = WD.lab (τ k) (t k v) a
  rw [hγ]

end

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyWdSideOfTie
section
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host NumberField IsDedekindDomain Polynomial GlobalTheory.Pst

def CharSide.ofTied {D : D7} {C : CharFrame D} {nch : NChoice D} {Tp : TupTied D C nch} (T : NCharTied D C nch Tp) : CharSide D C :=
  { T with }

def CharSide.tied {D : D7} {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch) (S : CharSide D C)
    (h : ∀ i (j : Fin D.R.m), j.1 + 1 = D.nd.j i → (S.e1 (D.naut.muC i)).1 = Tp.tup (D.nd.mu i) j) : NCharTied D C nch Tp :=
  { S with muC := h }

def RowSide.ofLoc (D : D7) (i : D.nd.Loc) : RowSide D :=
  ⟨D.naut.locW i, D.naut.satW i, D.naut.lab_loc i⟩

theorem exists_bridges (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω) (hpl : ∀ w, IsPlaceOver (pl w) w) :
    ∃ (LL : FinExt l) (br : ∀ w : HeightOneSpectrum (𝓞 E), w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (pl w)) ↥(OL LL)),
      ∀ w hw, Induces (br w hw) := by
  have hfin : (placesOver E l).Finite := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
      simpa using (Fact.out : l.Prime).ne_zero
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.mpr hv
  have := hfin.to_subtype
  choose j L0 hj hL using fun w : placesOver E l => GlobalTheory.PlaceBridge.exists_locBridge l E Ω w.1 (pl w.1) w.2 (hpl w.1)
  have := fun w => (L0 w).2
  let LL : FinExt l := ⟨⨆ w, (L0 w).1, inferInstance⟩
  choose br hb using fun w => hL w LL (le_iSup (fun w => (L0 w).1) w)
  exact ⟨LL, fun w hw => br ⟨w, hw⟩, fun w hw x => by rw [(hb _).1]; exact hj ⟨w, hw⟩ x⟩

theorem localPreds_of_isModel {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
    {pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω}
    {br : ∀ w : HeightOneSpectrum (𝓞 E), w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (pl w)) O}
    (hpl : ∀ w, IsPlaceOver (pl w) w) (hbr : ∀ w hw, Induces (br w hw))
    {m : ℕ} {r : G E Ω →* GL (Fin m) (Om l)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : w ∈ placesOver E l) (B : LocBridge l E Ω (Dec (F := E) (pl w)) O') (hB : Induces B)
    {L : FinExt l} {r' : ↥(Dec (F := E) (pl w)) →* GL (Fin m) ↥L.1}
    (h : IsModel B (resDec pl r w) L r') :
    (IsCrysW P pl br r w ↔ B.IsCrysE P L r') ∧
    (IsdRW P pl br r w ↔ B.IsdRE P L r') ∧
    (IsPotCrysW P pl br r w ↔ B.IsPotCrysE P L r') ∧
    ∀ (τ : E →+* Om l) (τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥L.1), IsInduced B τ τ' →
      (B.IsdRE P L r' → ∀ a : ℤ, a ∈ jumpsW P pl br r τ ↔ B.IsJumpE P L r' τ' a) ∧
      (B.IsdRE P L r' → ∀ a : ℤ, ((jumpsW P pl br r τ).count a : ℤ) = B.multE P L r' τ' a) := by
  have := L.2
  have := (br w hw).LL.2
  let L' : FinExt l := ⟨L.1 ⊔ (br w hw).LL.1, inferInstance⟩
  have l₁ : L.1 ≤ L'.1 := le_sup_left
  have l₂ : (br w hw).LL.1 ≤ L'.1 := le_sup_right
  have h' : IsModel (br w hw) (resDec pl r w) L' (mapRep (IntermediateField.inclusion l₁).toRingHom r') :=
    ⟨l₂, (h.enlarge l₁).2⟩
  obtain ⟨a₁, b₁, c₁, d₁⟩ := local_of_isModel P hpl hbr h'
  obtain ⟨a₂, b₂, c₂, d₂⟩ := bridge_indep l P E Ω (pl w) O O' (br w hw) B (hbr w hw) hB L' l₂ m (mapRep (IntermediateField.inclusion l₁).toRingHom r')
  obtain ⟨a₃, b₃, c₃, d₃⟩ := local_ext P B l₁ r'
  have key : ∀ (τ : E →+* Om l) (τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥L.1), IsInduced B τ τ' → B.IsdRE P L r' →
      ∀ a : ℤ, ((jumpsW P pl br r τ).count a : ℤ) = B.multE P L r' τ' a := fun τ τ' hτ hd a => by
    obtain ⟨τ₁, t₁, e⟩ := d₂ τ ((IntermediateField.inclusion l₁).comp τ') hτ
    rw [(d₁ τ τ₁ t₁).2 (b₂.2 (b₃.2 hd)), e, d₃]
  refine ⟨a₁.trans (a₂.trans a₃), b₁.trans (b₂.trans b₃), c₁.trans (c₂.trans c₃), fun τ τ' hτ => ⟨fun hd a => ?_, key τ τ' hτ⟩⟩
  rw [isJumpE_iff P hd, ← key τ τ' hτ hd a, ← Multiset.count_ne_zero]
  exact Nat.cast_ne_zero.symm

theorem localPreds_of_bridge {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
    {pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω}
    {br : ∀ w : HeightOneSpectrum (𝓞 E), w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (pl w)) O}
    (hpl : ∀ w, IsPlaceOver (pl w) w) (hbr : ∀ w hw, Induces (br w hw)) {w : HeightOneSpectrum (𝓞 E)}
    (hw : w ∈ placesOver E l) (B : LocBridge l E Ω (Dec (F := E) (pl w)) O') (hB : Induces B)
    (φ : O' →+* Om l) (hφ : ∀ x, φ x = ((B.toLL x : ↥B.LL.1) : Om l)) :
    (∀ (m : ℕ) (ρ : G E Ω →* GL (Fin m) O'),
      (IsCrysW P pl br (mapRep φ ρ) w ↔ B.IsCrysW P (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (IsdRW P pl br (mapRep φ ρ) w ↔ B.IsdRW P (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (IsPotCrysW P pl br (mapRep φ ρ) w ↔ B.IsPotCrysW P (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (∀ (τ : E →+* Om l) (τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥B.LL.1), IsInduced B τ τ' →
        (B.IsdRW P (ρ.comp (Dec (F := E) (pl w)).subtype) → ∀ a : ℤ,
          a ∈ jumpsW P pl br (mapRep φ ρ) τ ↔ B.IsJumpW P (ρ.comp (Dec (F := E) (pl w)).subtype) τ' a) ∧
        (B.IsdRW P (ρ.comp (Dec (F := E) (pl w)).subtype) → ∀ a : ℤ,
          ((jumpsW P pl br (mapRep φ ρ) τ).count a : ℤ) = B.multW P (ρ.comp (Dec (F := E) (pl w)).subtype) τ' a))) ∧
    ∀ (LL' : FinExt l), B.LL.1 ≤ LL'.1 → ∀ (m : ℕ) (ρ : G E Ω →* GL (Fin m) ↥LL'.1),
      (IsCrysW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) w ↔ B.IsCrysE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (IsdRW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) w ↔ B.IsdRE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (IsPotCrysW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) w ↔ B.IsPotCrysE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (∀ (τ : E →+* Om l) (τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced B τ τ' →
        (B.IsdRE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype) → ∀ a : ℤ,
          a ∈ jumpsW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) τ ↔ B.IsJumpE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype) τ' a) ∧
        (B.IsdRE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype) → ∀ a : ℤ,
          ((jumpsW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) τ).count a : ℤ) =
            B.multE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype) τ' a)) := by
  refine ⟨fun m ρ => ?_, fun LL' hL m ρ => ?_⟩
  · have h : IsModel B (resDec pl (mapRep φ ρ) w) B.LL (mapRep B.toLL (ρ.comp (Dec (F := E) (pl w)).subtype)) :=
      ⟨le_rfl, by ext g i j; exact (hφ _).symm⟩
    obtain ⟨a, b, c, d⟩ := localPreds_of_isModel P hpl hbr hw B hB h
    exact ⟨a, b, c, d⟩
  · have h : IsModel B (resDec pl (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) w) LL' (ρ.comp (Dec (F := E) (pl w)).subtype) := ⟨hL, rfl⟩
    exact localPreds_of_isModel P hpl hbr hw B hB h

set_option maxHeartbeats 1000000 in

theorem nonempty_wdSide_of_tie (hB : GlobalTheory.Published.DeRhamPotSemistable) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) : Nonempty (WDSide D T) := by
  classical
  choose LL br hbr using fun (l : ℕ) (hl : Fact l.Prime) => exists_bridges l D.host.E D.nd.Om D.nd.plOm.1 D.nd.plOm.2
  let wd : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a}, (G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) → ∀ w, D.naut.LP w :=
    fun l hl ι a r w => (T.e w).symm (if hw : w ∈ placesOver D.host.E l then
      wdL (D.loc l) ι D.nd.plOm.1 (br l hl) r D.nd.plOm.2 (hbr l hl) w hw else GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι r)
  have h1 : ∀ (l : ℕ) [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w
      (hw : w ∈ placesOver D.host.E l), T.e w (wd l ι r w) = wdL (D.loc l) ι D.nd.plOm.1 (br l hl) r D.nd.plOm.2 (hbr l hl) w hw :=
    fun l hl ι a r w hw => by simp only [wd, Equiv.apply_symm_apply, dif_pos hw]
  have h2 : ∀ (l : ℕ) [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w
      (hw : w ∉ placesOver D.host.E l), T.e w (wd l ι r w) = GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι r :=
    fun l hl ι a r w hw => by simp only [wd, Equiv.apply_symm_apply, dif_neg hw]
  have hL := fun (l : ℕ) [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w hw =>
    GlobalTheory.PstLaws.wdL_laws hB l (D.loc l) (D.locA l) (D.locT l) ι D.host.E D.nd.Om _ D.nd.plOm.1 (br l hl) D.nd.plOm.2 (hbr l hl) r w hw
  have hA := fun (l : ℕ) [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w
    (hw : w ∉ placesOver D.host.E l) => GlobalTheory.WeilDeligne.wdOf_laws (D.nd.plOm.2 w) hw ι r
  refine ⟨{
    wdOf := wd
    wdOf_dim := fun l hl ι a r w => ?_
    wdOf_unr := fun l hl ι a r w hw hc => by rw [T.unr, h2 l ι r w hw]; exact ((hA l ι r w hw).2 hc).2.2.1
    wdOf_frob := fun l hl ι a r w hw hc hu B σ hp hσ => ?_
    wdOf_ine := fun l hl ι a r w hw hc σ hσ => by rw [T.inePol _ _ σ hσ, h2 l ι r w hw]; exact ((hA l ι r w hw).2 hc).2.2.2.2.1 σ hσ
    wdOf_mono0 := fun l hl ι a r w hw hc => by rw [T.mono0, h2 l ι r w hw]; exact ((hA l ι r w hw).2 hc).2.2.2.2.2
    IsCrysW := fun l hl _ _ r w => IsCrysW (D.loc l) D.nd.plOm.1 (br l hl) r w
    IsPotCrysW := fun l hl _ _ r w => IsPotCrysW (D.loc l) D.nd.plOm.1 (br l hl) r w
    IsdRW := fun l hl _ _ r w => IsdRW (D.loc l) D.nd.plOm.1 (br l hl) r w
    jumpsW := fun l hl _ _ r τ => jumpsW (D.loc l) D.nd.plOm.1 (br l hl) r τ
    wdOf_unrL := fun l hl ι a r w hw hc hd => by rw [T.unr, h1 l ι r w hw]; exact ((hL l ι r w hw).2 hc hd).1
    wdOf_mono0L := fun l hl ι a r w hw hc hd => by rw [T.mono0, h1 l ι r w hw]; exact ((hL l ι r w hw).2 hc hd).2
    away := fun l hl ι a r w hw => h2 l ι r w hw
    above := fun l hl ι a r w hw => ⟨_, br l hl w hw, hbr l hl w hw, h1 l ι r w hw⟩
    loc := fun l hl ι w hw O _ _ _ Bw hj φ hφ => ⟨fun m ρ _ => ?_, fun LL' hL' m ρ _ => ?_⟩ }⟩
  · rw [← T.dim]
    by_cases hw : w ∈ placesOver D.host.E l
    · rw [h1 l ι r w hw]; exact (hL l ι r w hw).1
    · rw [h2 l ι r w hw]; exact (hA l ι r w hw).1
  · rw [T.frobEig _ _ hu, h2 l ι r w hw]
    rw [T.unr, h2 l ι r w hw] at hu
    exact ((hA l ι r w hw).2 hc).2.2.2.1 hu B σ hp hσ
  · exact (localPreds_of_bridge (D.loc l) D.nd.plOm.2 (hbr l hl) hw Bw hj φ hφ).1 m ρ
  · exact (localPreds_of_bridge (D.loc l) D.nd.plOm.2 (hbr l hl) hw Bw hj φ hφ).2 LL' hL' m ρ

end GlobalTheory.HeightCounting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationSquaresAgreeAtEachThickening
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

open SqLevel in
set_option maxHeartbeats 400000 in

theorem polarisation_squares_agree_at_level : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      eSec G (r z) ∈ U.LG.L.U jL → eSec G (r z) ∈ U'.LG.L.U jL' →
      gm r z _ (U.LG.rig.s (fun _ => jL)) ^ 2 =
        gv wL (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') * gm r z _ (U'.LG.rig.s (fun _ => jL')) ^ 2) →
    ∀ (e : ℕ) (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A), IsMonHom β.hom →
    (U'.gt e).q ≫ β.hom = (U.gt e).q →
    ∃ v : LB.Iso ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
        (fstG I e D'.toPre.P.A).left)
      ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
        (β.hom.left ≫ (fstG I e D.toPre.P.A).left)), v.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
      (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
      (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
      gw v (r ≫ (U'.gt e).q.left) z (fun _ => jM) (fun _ => fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 =
        gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG I e G).left) z (fun _ => jL) (fun _ => jL') := by
  intro hG R _ _ _ I hI D D' A A' G _ _ hS U U' wL hwL hrig e β hβ hq
  have hM := DVR.linComb_isLB D.toPre.P.L D.toPre.P.isLB (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)
  have hM' := DVR.linComb_isLB D'.toPre.P.L D'.toPre.P.isLB (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)
  have hL := DVR.linComb_isLB U.LG.L U.LG.isLB (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)
  have hL' := DVR.linComb_isLB U'.LG.L U'.LG.isLB (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)
  have hwL' : (isoPullId wL (rfl : 𝟙 G.left = 𝟙 G.left)).IsGen := (isGen_iff _).2 (isoPullId_pgen hwL rfl)
  obtain ⟨u, hu, hu'⟩ := LevelComparison.exists_comparison hM hM' hL hL' (sqIso_isGen (U.w_gen e))
    (sqIso_isGen (U'.w_gen e)) hwL'
  have sqrel : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι)
      (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
      (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
      gw u r z (fun _ => jM) (fun _ _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 =
        gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG I e G).left) z (fun _ => jL) (fun _ => jL') := by
    intro Z r z jM jM' jL jL' a₁ a₂ a₃ a₄
    have h := hu' Z r z (fun _ => jM) (fun _ => jM') (fun _ => jL) (fun _ => jL') (mem_sq.2 a₁) (mem_sq.2 a₂)
      (mem_sq.2 a₃) (mem_sq.2 a₄)
    rw [gw_sqIso (U'.w e) r z (fun _ => jM') (fun _ _ => jL') a₂ a₄,
      gw_sqIso (U.w e) r z (fun _ => jM) (fun _ _ => jL) a₁ a₃,
      gw_isoPullId wL rfl _ z (fun _ => jL) (fun _ => jL') (mem_sq.2 a₃) (mem_sq.2 a₄)] at h
    exact h
  have inv := GlobalTheory.T.square_comparison_torus_invariant hG R I hI D D' A A' G hS U U' wL hwL (GlobalTheory.T.square_iso_carries_square_cubical hG R I hI D D' A A' G hS U U' wL hwL)
    (GlobalTheory.T.square_iso_respects_symmetry_pointwise hG R I hI D D' A A' G hS U U' wL hwL) e β hβ hq u hu sqrel
  haveI := (U'.gt e).q_flat
  haveI := (U'.gt e).q_surj
  haveI := (U'.gt e).q_affine
  haveI := (U.gt e).q_hom
  have hql : (U'.gt e).q.left ≫ β.hom.left = (U.gt e).q.left := congrArg (·.left) hq
  obtain ⟨v, hv, hv'⟩ := LevelComparison.exists_iso_descend (U'.gt e).q.left (fstG I e D'.toPre.P.A).left
    (β.hom.left ≫ (fstG I e D.toPre.P.A).left) (p := (U.gt e).pG.left) (p' := (U'.gt e).pG.left)
    (by rw [← Category.assoc, hql]; rfl) rfl u hu (fun Z g₁ g₂ z j j' h a b => by
      obtain ⟨a₀, rfl⟩ : ∃ a₀, j = fun _ => a₀ := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim k 0)⟩
      obtain ⟨b₀, rfl⟩ : ∃ b₀, j' = fun _ => b₀ := ⟨j' 0, funext fun k => congrArg j' (Subsingleton.elim k 0)⟩
      let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (g₂ ≫ (thickObj R I e G).hom)
      let k₂ : Z' ⟶ thickObj R I e G := Over.homMk g₂ rfl
      let k₁ : Z' ⟶ thickObj R I e G := Over.homMk g₁ (by
        change g₁ ≫ (thickObj R I e G).hom = g₂ ≫ (thickObj R I e G).hom
        rw [← Over.w (U'.gt e).q, reassoc_of% h])
      have e₁ : k₁ ≫ (U'.gt e).q = k₂ ≫ (U'.gt e).q := Over.OverMorphism.ext h
      have e' : k₁ ≫ (U.gt e).q = k₂ ≫ (U.gt e).q := by rw [← hq, reassoc_of% e₁]
      have w : (k₁ * k₂⁻¹) ≫ (U.gt e).q = toUnit Z' ≫ η[thickObj R I e D.toPre.P.A] := by
        rw [MonObj.mul_comp, GrpObj.inv_comp, e', mul_inv_cancel]
        rfl
      have ht : ((U.gt e).isKernel.lift _ _ w ≫ (U.gt e).i) * k₂ = k₁ := by
        rw [(U.gt e).isKernel.lift_fst, inv_mul_cancel_right]
      have := inv Z' ((U.gt e).isKernel.lift _ _ w) k₂ z a₀ b₀ (mem_sq.1 a) (mem_sq.1 b)
      rw [ht] at this
      exact this)
  refine ⟨v, hv, fun Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  rw [hv' Z r z (fun _ => jM) (fun _ => jM') (mem_sq.2 a₁) (mem_sq.2 a₂)]
  exact sqrel Z r z jM jM' jL jL' a₁ a₂ a₃ a₄

end GlobalTheory
end
end

