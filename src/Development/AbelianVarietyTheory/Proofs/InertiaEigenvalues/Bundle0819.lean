import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0060
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0100
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodIdempotentFixesMemGoodTypeSpace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatHeckeRealRd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie.HkRat

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks}
  {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem evK_hkFR {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL ((j : ℕ) + 1)))
    (hs : NX.HeckeStabR S ((j : ℕ) + 1) hL) (k : ℕ) (P : PlE D.host) (R : Finset (GA D (Wc D j))) (s : ℂ)
    (hR : ∀ x : S.WL ((j : ℕ) + 1), evW YS v₀ j (hL k P x) = s • heckeLin (Wc D j) R (evW YS v₀ j x))
    (y : NX.Fm S i ((j : ℕ) + 1) b) :
    evK YS v₀ hρ i j b (NX.hkFR S i ((j : ℕ) + 1) b hL hs k P y) = s • heckeLin (Wc D j) R (evK YS v₀ hρ i j b y) := by
  induction y using TensorProduct.induction_on with
  | zero => erw [LinearMap.map_zero, map_zero, map_zero, smul_zero]
  | add y z hy hz => erw [LinearMap.map_add, map_add, hy, hz, map_add, map_add, smul_add]
  | tmul a f0 =>
    have e1 : NX.hkFR S i ((j : ℕ) + 1) b hL hs k P (a ⊗ₜ f0) =
        a ⊗ₜ (((hL k P).restrictScalars S.Ks).restrict (p := (S.A ((j : ℕ) + 1)).WK) (q := (S.A ((j : ℕ) + 1)).WK)
          fun x hx => hs k P x hx) f0 := rfl
    erw [e1, evK_tmul, evK_tmul]
    change ρ.e i b a • evW YS v₀ j (hL k P f0.1) = _
    rw [hR, map_smul, smul_comm]

end GlobalTheory.SeriesTie.HkRat

namespace GlobalTheory.SeriesTie.HkRat

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks}
  {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem evW_reads (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (hR : GlobalTheory.ExportPin.Reads Rl cG S YS hL)
    (j : Fin D.R.m) (k : ℕ) (P : PlE D.host) (hPs : IsSplitPl D.host P)
    (hso : Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E))) (hk : k ≤ D.R.r) (α : GA D (Wc D j)) (R : Finset (GA D (Wc D j)))
    (hα : IsHeckeAt (Wc D j) P k α) (hdc : Bridge.IsDC (levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv)) α R)
    (x : S.WL ((j : ℕ) + 1)) :
    evW YS v₀ j (hL ((j : ℕ) + 1) k P x) =
      ((((Rl.C.mu0 j).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) •
        heckeLin (Wc D j) R (evW YS v₀ j x) := by
  have h := congrArg (fun F => F (v₀ j (sg0 D A3.A))) (hR j k P hPs hso hk α R hα hdc x)
  exact h

end GlobalTheory.SeriesTie.HkRat

namespace GlobalTheory.SeriesTie.HkRat
open GlobalTheory.SeriesTie.Setup

theorem ratHecke_realRd : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ), RealPin Rl cG ρ → ChrEq (Rl.mu0 ((j : ℕ) + 1)) (Rl.C.mu0 j) → (∀ P, IsSplitPl D.host P → P ∉ D.ntw.S0 i → Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E))) → ∀ hL : ∀ n, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL n), NX.HeckeStabR S ((j : ℕ) + 1) (hL ((j : ℕ) + 1)) → GlobalTheory.ExportPin.Reads Rl cG S YS hL → RatHecke (realRd YS v₀ hρ i j b ν) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG S YS v₀ ρ hρ i j b ν hp hchr hsplit hL hs hR k P hk f
  obtain ⟨hk1, hkr, hPs, hPS0⟩ := hk
  have hso := hsplit P hPs hPS0
  have hPg : Bridge.SplitOff P (((ρ.B i j b).G.Pg : Finset _) : Set (Pl D.host.E)) :=
    GlobalTheory.T.split_off_outside_S0 hρ i _ (fun P' hP' => by
      obtain ⟨k', hk'⟩ := hρ.Pg i j b P' hP'
      exact D.ntw.placesOver_subset_exceptional i k' hk') P hPs hPS0
  have hdQ : Bridge.SplitOff P (((ρ.B i j b).de.Q : Finset _) : Set (Pl D.host.E)) :=
    GlobalTheory.T.split_off_outside_S0 hρ i _ (fun P' hP' => by
      rw [hρ.delta i j b] at hP'
      exact D.ntw.primes_subset_exceptional i (mem_half.1 hP').1) P hPs hPS0
  by_cases hd : ∃ α R z, ρ.IsHeckeDatum i j b k P α R z
  swap
  · exact ⟨0, fun α R z d => absurd ⟨α, R, z, d⟩ hd⟩
  obtain ⟨α₀, R₀, z₀, d₀⟩ := hd
  obtain ⟨a, ha⟩ := GlobalTheory.T.twisting_char_values_mem_coeff_field_range hρ i j b z₀
  have hde : ∀ α R z, ρ.IsHeckeDatum i j b k P α R z → (((ρ.B i j b).de.chi z : Circle) : ℂ) = ρ.e i b a :=
    fun α R z d => by
      rw [ha, GlobalTheory.T.heckeCharacter_value_at_splitPlace_determinant _ _ _ _ P k α z (hp.delta i j b) (hρ.base i j b).de.unram (hρ.base i j b).de.split hdQ d.elt d.det,
        GlobalTheory.T.heckeCharacter_value_at_splitPlace_determinant _ _ _ _ P k α₀ z₀ (hp.delta i j b) (hρ.base i j b).de.unram (hρ.base i j b).de.split hdQ d₀.elt d₀.det]
  have hchr' : ChrEq (ρ.B i j b).mu0 (Rl.C.mu0 j) := by rw [hp.mu0 i j b]; exact hchr
  have hmu0 : ∀ α R z, ρ.IsHeckeDatum i j b k P α R z →
      (((ρ.B i j b).mu0 z : Circle) : ℂ) = (((Rl.C.mu0 j).val P : ℂˣ) : ℂ) ^ k :=
    fun α R z d => GlobalTheory.T.heckeCharacter_value_at_splitPlace_determinant _ _ _ _ P k α z hchr' (hρ.base i j b).unram
      ((hρ.base i j b).places.split.elim fun _ h => h.2.2.mono h.1) hPg d.elt d.det
  refine ⟨a⁻¹ • (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm
    (NX.hkFR S i ((j : ℕ) + 1) b (hL _) hs k P (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)), ?_⟩
  rcases eq_or_ne ν 0 with rfl | hν
  · intro α R z d
    rw [realRd_apply, realRd_apply YS v₀ hρ i j b 0 f, inv_zero, zero_smul, zero_smul, map_zero]
  rw [heckeAt_realRd YS v₀ hρ i j b hν]
  intro α R z d
  have hdc := d.reps
  rw [GlobalTheory.T.complex_principal_level_eq_realisation_principal_level Rl hp i j b] at hdc
  have key := evK_hkFR YS v₀ hρ i j b (hL _) hs k P R _
    (evW_reads YS v₀ hL hR j k P hPs hso hkr α R d.elt hdc) (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)
  funext x
  rw [Setup.hecke_apply, map_smulₛₗ]
  change ρ.e i b a⁻¹ * ((1 : ℂ)⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2
    ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm _))) x = _ * _ *
      ∑ γ ∈ R, ((1 : ℂ)⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)) (x * γ)
  rw [LinearEquiv.apply_symm_apply, key]
  simp only [inv_one, one_smul, Pi.smul_apply, smul_eq_mul, heckeLin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Base.mu, MonoidHom.mul_apply, Circle.coe_mul, hmu0 α R z d, hde α R z d, map_inv₀]
  rw [show normV P = Nat.card (kP P) from rfl, D.sp.V_rank _ (Nat.le_add_left _ _) j.2]
  simp only [one_mul]
  ring

end GlobalTheory.SeriesTie.HkRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeDifferentOrderBoundedAbsoluteRamificatio
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

namespace GlobalTheory.TowerDifferent

theorem not_pow_dvd_differentIdeal_int : ∀ (L : Type) [Field L] [NumberField L] (l e : ℕ), l.Prime → ∀ (la : Ideal (𝓞 L)) [la.IsPrime], la ≠ ⊥ → ((l : ℕ) : 𝓞 L) ∈ la → ((l : ℕ) : 𝓞 L) ∉ la ^ (e + 1) → ¬ la ^ (e * e + 1) ∣ differentIdeal ℤ (𝓞 L) := by
  intro L _ _ l e hl la _ hla h1 h2 hD
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : la.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hla
  obtain ⟨e', J, he0, hee, hcop, hfac⟩ := GlobalTheory.T.exists_span_prime_eq_pow_mul_coprime L l e hl la h1 h2
  obtain ⟨hchar, hfin, ϖ, hϖ, hlϖ, hcard⟩ := GlobalTheory.T.quotient_pow_finite_uniformizer_card_eq L la J l e' e' hl he0 he0 hcop hfac
  letI : Algebra (ZMod (l ^ e')) (𝓞 L ⧸ la ^ (e' * e')) := ZMod.algebra _ _
  have hnd : ¬ l ^ e' ∣ e' := fun h => (Nat.lt_pow_self hl.one_lt).not_ge (Nat.le_of_dvd he0 h)
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_trace_ne_zero_finite_local_zmod_prime_pow l e' e' (𝓞 L ⧸ la ^ (e' * e')) ϖ he0 hϖ hlϖ hcard hnd
  obtain ⟨c0, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hIQ : la ^ (e' * e') ⊔ J ^ e' = ⊤ := by
    have h' : IsCoprime la J := Ideal.isCoprime_iff_sup_eq.mpr hcop
    exact Ideal.isCoprime_iff_sup_eq.mp (h'.pow)
  have hmul : la ^ (e' * e') * J ^ e' = Ideal.span {((l ^ e' : ℕ) : 𝓞 L)} := by
    rw [pow_mul, ← mul_pow, ← hfac, Ideal.span_singleton_pow, Nat.cast_pow]
  obtain ⟨i, hi, q, hq, hiq⟩ : ∃ i ∈ la ^ (e' * e'), ∃ q ∈ J ^ e', i + q = 1 := by
    have : (1 : 𝓞 L) ∈ la ^ (e' * e') ⊔ J ^ e' := hIQ ▸ Submodule.mem_top
    exact Submodule.mem_sup.mp this
  have hx : q * c0 ∈ J ^ e' := Ideal.mul_mem_right _ _ hq
  have hxc : Ideal.Quotient.mk (la ^ (e' * e')) (q * c0) = Ideal.Quotient.mk (la ^ (e' * e')) c0 := by
    rw [Ideal.Quotient.eq]
    have : q * c0 - c0 = -(i * c0) := by linear_combination c0 * hiq
    rw [this]; exact neg_mem (Ideal.mul_mem_right _ _ hi)
  have htr := GlobalTheory.T.intCast_trace_eq_trace_quotient_of_mem' L l e' (la ^ (e' * e')) (J ^ e') hIQ hmul (q * c0) hx
  rw [hxc] at htr
  have hnot : Algebra.intTrace ℤ (𝓞 L) (q * c0) ∉ Ideal.span {((l ^ e' : ℕ) : ℤ)} := by
    intro hm
    rw [Algebra.intTrace_eq_trace, Ideal.mem_span_singleton] at hm
    apply hc
    rw [← htr, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast hm)]
  have hmap : la ^ (e' * e') * J ^ e' = Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {((l ^ e' : ℕ) : ℤ)}) := by
    rw [hmul, Ideal.map_span, Set.image_singleton, map_natCast]
  have := not_dvd_differentIdeal_of_intTrace_not_mem (A := ℤ) (la ^ (e' * e')) (J ^ e') hmap (q * c0) hx hnot
  apply this
  refine dvd_trans (pow_dvd_pow _ ?_) hD
  have := Nat.mul_le_mul hee hee
  omega

theorem differentIdeal_dvd_int (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    differentIdeal (𝓞 K) (𝓞 L) ∣ differentIdeal ℤ (𝓞 L) := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 K) (𝓞 L)]
  exact dvd_mul_right _ _

theorem relDifferent_order_bounded : ∀ (l e : ℕ), l.Prime → ∃ c : ℕ, ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : HeightOneSpectrum (𝓞 K)) (la : HeightOneSpectrum (𝓞 L)), la.asIdeal.under (𝓞 K) = p.asIdeal → ((l : ℕ) : 𝓞 L) ∈ la.asIdeal → ((l : ℕ) : 𝓞 L) ∉ la.asIdeal ^ (e + 1) → ¬ la.asIdeal ^ (c + 1) ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  intro l e hl
  refine ⟨e * e, ?_⟩
  intro K L _ _ _ _ _ p la _ h1 h2 h3
  exact not_pow_dvd_differentIdeal_int L l e hl la.asIdeal la.ne_bot h1 h2 (dvd_trans h3 (differentIdeal_dvd_int K L))

end GlobalTheory.TowerDifferent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowParamOfCuspidal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs

theorem rowParam_of_cuspParam : ∀ (D : D7) (Rw : RowSide D), GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → D.ntypes.cuspidal σ) → (∀ k v, IsSplitPl D.host (D.naut.plGw k v)) → RowParam D Rw := by
  intro D Rw hP hC hS j hj1 hj2 σ hσ hg
  obtain ⟨π, h⟩ := hP j hj1 hj2 σ hσ hg
  have hembb : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ = GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ true := fun τ => by
    ext x
    have e : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ true x = starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ false x) :=
      D.host.conjE_apply (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ false) x
    rw [e]
    rfl
  have hpar : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ) = (GlobalTheory.Triple.rowPar (D.hc τ)).map (fun p => ((p : ℚ) : ℂ)) := by
    intro τ
    simp [GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma, GlobalTheory.Triple.rowPar, Multiset.map_add, Multiset.map_map, Function.comp_def]
  refine ⟨π, ⟨h.1, h.2.1, fun τ => ?_, fun w hw => h.unr w hw, fun k v => ?_, hC j hj1 hj2 σ hσ hg⟩, h.2.2.1⟩
  · obtain ⟨a, b⟩ := h.2.2.2.2.2 τ
    refine ⟨?_, ?_⟩
    · rw [← hpar]; exact a
    · rw [← hembb, b, hpar, Multiset.map_map]
      refine Multiset.map_congr rfl fun p _ => ?_
      simp
  · rw [Rw.lab_eq k σ v, h.2.2.1 _ (hS k v)]
end GlobalTheory.TwInputs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchrodingerFunctionInvariantTypePrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

namespace GlobalTheory.DownLift.GenSplit

theorem actO_sigma_of_grpCo : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i)), (∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X) → ∀ (κ : GA D (Vc D i)) (h : GL (Fin D.R.r ⊕ Fin D.R.t) (OI v)) (h' : GL (Fin (Vc D i).rank) (OI v)), (∀ a b, (h' : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (OI v)) (rowIx (rank_V i) a) (rowIx (rank_V i) b) = (h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)) a b) → grpCo φ (Vc D i) (frCo φ (R.βV i)) κ = Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h' → ∀ X : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v), actO (Vc D i) (Wc D i) κ 1 (σ X) = σ ((h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) * X) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL i v φ e he σ hσ κ h h' hh' hgrp X
  have sdV := GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i)
  have sdW := GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)
  have hco := (GlobalTheory.PlaceTensor.adjCo_isCoord D (Vc D i) (Wc D i) _ _ sdV sdW v φ e he
    (frCo φ (R.βV i)) (frCo φ (R.βW i))).1
  have hinj := hco.2.1.injOn
  have h1 : IsHalf (cA D e) (actO (Vc D i) (Wc D i) κ 1 (σ X)) := GlobalTheory.SplitHecke.isHalf_actO κ 1 (hσ X).1
  have h2 : IsHalf (cA D e) (σ ((h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) * X)) := (hσ _).1
  refine hinj h1 h2 ?_
  have ha : adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) (actO (Vc D i) (Wc D i) κ 1 (σ X)) =
      (grpCo φ (Vc D i) (frCo φ (R.βV i)) κ).val * adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) (σ X) := by
    have := GlobalTheory.PlaceTensor.AdjCoord.adjCo_actO φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) κ⁻¹ 1 (σ X)
    rw [inv_inv, inv_one, GlobalTheory.PlaceTensor.AdjCoord.grpCo_inv, inv_inv] at this
    rw [this]
    have g1 : grpCo φ (Wc D i) (frCo φ (R.βW i)) 1 = 1 := by
      unfold grpCo; rw [map_one, map_one, mul_one, inv_mul_cancel]
    rw [g1, Units.val_one, Matrix.mul_one]
  have hc : ∀ x, coR R i φ x = (adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) x).submatrix (rowIx (rank_V i)) (finCongr (rank_weight_component_eq i)) := fun x => rfl
  have hX : coR R i φ (actO (Vc D i) (Wc D i) κ 1 (σ X)) = coR R i φ (σ ((h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) * X)) := by
    rw [(hσ _).2, hc, ha, hgrp, ← Matrix.submatrix_mul_equiv _ _ _ (rowIx (rank_V i)), ← hc, (hσ X).2]
    congr 1
    ext a b
    simp [Matrix.GeneralLinearGroup.map, hh']
  refine Matrix.ext fun a b => ?_
  have e1 := congrFun (congrFun hX ((rowIx (rank_V i)).symm a)) ((finCongr (rank_weight_component_eq i)).symm b)
  simpa [hc] using e1

theorem levG_levChi_of_red : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E), PP ∈ R.Pg → ∀ (κ : GA D (Vc D i)), κ ∈ GfC (Vc D i) → finE (Vc D i) κ ∈ St (R.βV i) → ∀ (g : GL (Fin (Vc D i).rank) (kP PP)), redFn (R.βV i) PP (finE (Vc D i) κ) = g → (∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → PP' ≠ PP → redFn (R.βV i) PP' (finE (Vc D i) κ) = 1) → (∀ a b : Fin D.R.r, (g : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) (rowIx (rank_V i) (Sum.inl a)) (rowIx (rank_V i) (Sum.inl b)) = (1 : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) a b) → (∀ (a : Fin D.R.t) (b : Fin D.R.r), (g : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) (rowIx (rank_V i) (Sum.inr a)) (rowIx (rank_V i) (Sum.inl b)) = 0) → κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t) ∧ levChi (Vc D i) (R.βV i) (R.datVt i t) κ = ((R.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL i t PP hPP κ hGf hSt g hg hoth hg1 hg2
  have rV : (Vc D i).rank = D.R.r + D.R.t := (rank_V i).symm
  have hdisj : PP ∉ R.Q t := Finset.disjoint_left.1 (Formalism.IndefR.Fin.disjoint_Pg_Q R.toLevCh hL t) hPP
  have hlo : ∀ a : Fin (Vc D i).rank, (ha : a.val < D.R.r) → a = rowIx (rank_V i) (Sum.inl ⟨a.val, ha⟩) := by
    intro a ha; ext; simp [rowIx]
  have hhi : ∀ a : Fin (Vc D i).rank, (ha : D.R.r ≤ a.val) →
      a = rowIx (rank_V i) (Sum.inr ⟨a.val - D.R.r, by have := a.2; omega⟩) := by
    intro a ha; ext; simp [rowIx]; omega
  have htri : g ∈ blockTri (blkOf D.R.r D.R.t) := by
    intro a b hab
    have ha : D.R.r ≤ a.val := by
      by_contra h; push_neg at h
      simp [blkOf, h] at hab
    have hb : b.val < D.R.r := by
      by_contra h; push_neg at h
      have h1 := a.2; have h2 := b.2
      have e1 : (a.val - D.R.r) / D.R.t = 0 := Nat.div_eq_of_lt (by omega)
      have e2 : (b.val - D.R.r) / D.R.t = 0 := Nat.div_eq_of_lt (by omega)
      simp [blkOf, not_lt.2 ha, not_lt.2 h, e1, e2] at hab
    rw [hhi a ha, hlo b hb]
    exact hg2 _ _
  have hr1 : upperLeftBlock (r_le_V i) g = 1 := by
    apply Units.ext
    rw [upper_block_val_submatrix _ (blockTri_blkOf_le _ _ htri), Units.val_one]
    refine Matrix.ext fun a b => ?_
    simp only [Matrix.submatrix_apply]
    have ea : Fin.castLE (r_le_V i) a = rowIx (rank_V i) (Sum.inl a) := by ext; simp [rowIx]
    have eb : Fin.castLE (r_le_V i) b = rowIx (rank_V i) (Sum.inl b) := by ext; simp [rowIx]
    rw [ea, eb, hg1]
  have hred : ∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → redFn (R.βV i) PP' (finE (Vc D i) κ) = 1 ∨ PP' = PP := by
    intro PP' h
    by_cases e : PP' = PP
    · exact Or.inr e
    · exact Or.inl (hoth PP' h e)
  have hrT : rTup (R.βV i) (R.datVt i t) (finE (Vc D i) κ) = 1 := by
    funext PP'
    show upperLeftBlock (r_le_V i) (redFn (R.βV i) PP'.1 (finE (Vc D i) κ)) = 1
    rcases hred PP'.1 (Or.inl PP'.2) with h | h
    · rw [h]; exact blockDiagonalExtendByOnePrimeField_one _ _
    · rw [h, hg, hr1]
  have hpar : finE (Vc D i) κ ∈ parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := by
    refine mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hSt, fun PP' hP' => ?_, fun PP' hP' => ?_⟩
    · rcases hred PP' (Or.inl hP') with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h, hg]; exact htri
    · rcases hred PP' (Or.inr hP') with h | h
      · rw [h]; exact Subgroup.one_mem _
      · exact absurd (h ▸ hP') hdisj
  refine ⟨⟨hGf, hpar, ?_⟩, ?_⟩
  · show rTup (R.βV i) (R.datVt i t) (finE (Vc D i) κ) ∈ (R.datVt i t).P.H
    rw [hrT]; exact Subgroup.one_mem _
  · have hQ : ∏ PP' ∈ (R.datVt i t).Q, (R.datVt i t).xq PP' (dBlk (blk2 (R.datVt i t).r) 1 (redFn (R.βV i) PP' (finE (Vc D i) κ))) = 1 := by
      refine Finset.prod_eq_one fun PP' hP' => ?_
      rcases hred PP' (Or.inr hP') with h | h
      · rw [h, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
      · exact absurd (h ▸ hP') hdisj
    have hdet : Matrix.GeneralLinearGroup.det g = dBlk (blkOf D.R.r D.R.t) 1 g := by
      rw [(GlobalTheory.T.det_twoDiagBlocks_properties _ _ _ D.R.t (r_le_V i) g).1 (blockTri_blkOf_le _ _ htri), hr1, map_one, one_mul,
        (GlobalTheory.T.det_twoDiagBlocks_properties _ _ _ D.R.t (r_le_V i) g).2.1 rV htri]
    have hG : ∏ PP' ∈ (R.datVt i t).Pg, ∏ c ∈ Finset.range (R.datVt i t).s, (R.datVt i t).cg (c + 1) PP'
        (dBlk (blkOf (R.datVt i t).r (R.datVt i t).t) (c + 1) (redFn (R.βV i) PP' (finE (Vc D i) κ))) =
        (R.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det g))⁻¹ := by
      rw [Finset.prod_eq_single PP]
      · show ∏ c ∈ Finset.range 1, _ = _
        rw [Finset.prod_range_one, hg, hdet]
        rfl
      · intro PP' hP' hne
        rcases hred PP' (Or.inl hP') with h | h
        · refine Finset.prod_eq_one fun c _ => ?_
          rw [h, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
        · exact absurd h hne
      · intro h; exact absurd hPP h
    unfold levChi levFn
    rw [hrT, blockDiagonalExtendByOnePrimeField_one, hQ, hG, one_mul, mul_one, Units.val_inv_eq_inv_val]

theorem heisO_smul_fun {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := by
  funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem schrodinger_type_inv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E), PP ∈ R.Pg → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsProjAt φ PP → IsIdemOf φ e → ∀ (red : OI v →+* kP PP), Function.Surjective red → (∀ a : OI v, red a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) → ActAt R i t PP φ e red → ∀ (Sb : Finset (FinPl D)), v ∈ Sb → ∀ (σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i)), (∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X) → ∀ (ℓ : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] ℂ), InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), TypeIn R i t Sb f → ∀ (ϖ : OI v), Irreducible ϖ → ∀ h : GL (Fin D.R.r ⊕ Fin D.R.t) (OI v), (∀ a b, (h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)) (Sum.inl a) (Sum.inl b) - (1 : Matrix (Fin D.R.r) (Fin D.R.r) (OI v)) a b ∈ Ideal.span {ϖ}) → (∀ a b, (h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)) (Sum.inr a) (Sum.inl b) ∈ Ideal.span {ϖ}) → ∀ X : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v), ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ ((h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) * X)) f) = ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ X) f) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hω i t PP hPP v φ e hφ he red hsur hker hAct Sb hv σ hσ ℓ hℓ f hf ϖ hϖ h hh1 hh2 X
  let e' := rowIx (rank_V i)
  let h' : GL (Fin (Vc D i).rank) (OI v) := Units.map (Matrix.reindexAlgEquiv (OI v) (OI v) e').toMonoidHom h
  have hh' : ∀ a b, (h' : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (OI v)) (e' a) (e' b) =
      (h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)) a b := by
    intro a b
    simp [h', Matrix.reindexAlgEquiv_apply]
  obtain ⟨κ, hsupp, hGf, hSt, hgrp, hred', hoth, hact⟩ := hAct h'
  have hϖ0 : red ϖ = 0 := by
    haveI : PP.asIdeal.IsMaximal := PP.isMaximal
    letI : Field (kP PP) := Ideal.Quotient.field _
    have hmax : RingHom.ker red = IsLocalRing.maximalIdeal (OI v) :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hsur)
    have : ϖ ∈ RingHom.ker red := by
      rw [hmax]; exact (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
    exact this
  have hspan : ∀ x ∈ Ideal.span {ϖ}, red x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, hϖ0, mul_zero]
  have hg1 : ∀ a b : Fin D.R.r, ((Matrix.GeneralLinearGroup.map red h' : GL (Fin (Vc D i).rank) (kP PP)) :
      Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) (e' (Sum.inl a)) (e' (Sum.inl b)) =
      (1 : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) a b := by
    intro a b
    have h0 := hspan _ (hh1 a b)
    rw [map_sub, sub_eq_zero] at h0
    rw [Matrix.GeneralLinearGroup.map_apply, hh', h0]
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.one_apply_ne hab]
  have hg2 : ∀ (a : Fin D.R.t) (b : Fin D.R.r), ((Matrix.GeneralLinearGroup.map red h' : GL (Fin (Vc D i).rank) (kP PP)) :
      Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) (e' (Sum.inr a)) (e' (Sum.inl b)) = 0 := by
    intro a b
    rw [Matrix.GeneralLinearGroup.map_apply, hh']
    exact hspan _ (hh2 a b)
  obtain ⟨hmem, hchi⟩ := levG_levChi_of_red D G Pl0 T A Ks R hL i t PP hPP κ hGf hSt _ hred' hoth hg1 hg2
  have hSIn : SuppIn Sb (Vc D i) κ := suppIn_of_suppAt he hv hsupp
  have hW := hω i t
  have hTy := hf.2 κ hmem hSIn
  rw [hchi, inv_inv] at hTy
  have hx := actO_sigma_of_grpCo D G Pl0 T A Ks R hL i v φ e he σ hσ κ h h' hh' hgrp X
  have e1 := hW.om_heis κ 1 (σ X) f hf.1
  rw [hx, hTy, heisO_smul_fun] at e1
  have e2 := hact ℓ hℓ (heisO R.ψ (Vc D i) (Wc D i) (σ X) f)
    (GlobalTheory.TwistFactorCompare.isTheta_heisO hW.std hf.1 _)
  rw [e1, map_smul, smul_eq_mul] at e2
  exact mul_left_cancel₀ (Units.ne_zero _) e2

end GlobalTheory.DownLift.GenSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideBKeep
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LamInstall
open ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NT

variable {D : D7} (hE : IsEmpty D.nd.Loc) {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)}
  {T : TwR D.LL0 D.nd} (Sp : RingSpec D cf b0 b1 Sx T) (F : TwF T)

abbrev recE (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)))
    (h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
    (th : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)) ex) : TwNew D :=
  ⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩

abbrev recL (L : TwL T) (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)))
    (h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
    (th' : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L) ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L))) :
    TwNew D :=
  ⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩

variable {hE Sp F} {L : TwL T} {ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T))}
  {h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g}
  {th : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)) ex}
  {th' : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L) ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L))}

set_option maxHeartbeats 4000000 in

def twFC (X : TwFrameC (recE hE Sp F ex h0 th).toD7) : TwFrameC (recL hE Sp F L ex h0 th').toD7 := { X with }

set_option maxHeartbeats 4000000 in

def expC (X : NExpTied (recE hE Sp F ex h0 th).toD7) : NExpTied (recL hE Sp F L ex h0 th').toD7 :=
  { X with
    mtV := fun i j b k Q ψ h1 h2 h =>
      letI := X.acgWt i j b
      letI : Module (FractionRing ((recL hE Sp F L ex h0 th').toD7.ntw.O i)) (X.Wt i j b) := X.modWt i j b
      { X.mtV i j b k Q ψ h1 h2 h with } }

set_option maxHeartbeats 4000000 in

theorem sideB_keep {Rw : RowSide D} {low : Finset ℕ}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
    {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}
    (B : SideB (recE hE Sp F ex h0 th).toD7 ((recE hE Sp F ex h0 th).cf cf) ((recE hE Sp F ex h0 th).row Rw) low Pq
      ((recE hE Sp F ex h0 th).rat S) hL eig θ)
    (chiI : ∀ s, L.abelian₂ s → NC.HC D.host.E)
    (hqs : ∀ i lam P, P ∉ T.S0 i →
      B.twF.iCq i (L.qs i lam P) = ((((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-(L.s2 i lam : ℝ) / 2) : ℝ) : ℂ))
    (hlam : ∀ s lam, NC.Read D.nd.plOm.1 (L.lamG s lam) (algebraMap (T.O s) (FractionRing (T.O s)))
      (B.chiD.embO s (L.sideL s lam)) (NC.complexEmbeddingRestrictedToSubfield D) (id (α := NC.HC D.host.E) (B.chiD.mu0 (L.jL s lam)) * id (α := NC.HC D.host.E) (B.chiD.del s) * (chiI s lam)⁻¹) 0) :
    Nonempty (SideB (recL hE Sp F L ex h0 th').toD7 ((recL hE Sp F L ex h0 th').cf cf) ((recL hE Sp F L ex h0 th').row Rw) low Pq
      ((recL hE Sp F L ex h0 th').rat S) hL eig θ) :=
  ⟨{ B with
      twF := twFC B.twF
      tw := { B.tw with qs_pos := hqs }
      chiD := { B.chiD with chiI := chiI }
      chi := { B.chi with lamG := hlam }
      exp := expC B.exp }⟩

end GlobalTheory.LamInstall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideBTies
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.SideTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fi
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def fiOf (R : RealDat3 D A3 Ks) (i' i : Fin D.R.m) (h : i' = i) : FormsIso (R.FW i') (R.FW i) := by
  subst h
  exact ⟨RingEquiv.refl _, fun _ => rfl, LinearEquiv.refl _ _, MulEquiv.refl _, fun _ => LinearIsometryEquiv.refl _ _,
    fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem fiOf_heq (R : RealDat3 D A3 Ks) (i' i : Fin D.R.m) (h : i' = i) (x : Fin (R.nW i') → D.what₂.LL) :
    HEq ((fiOf R i' i h).e x) x := by
  subst h; rfl

theorem fiOf_eG (R : RealDat3 D A3 Ks) (i' i : Fin D.R.m) (h : i' = i) (g : G) : (fiOf R i' i h).eG g = g := by
  subst h; rfl

end Fi

end GlobalTheory.TwInputs.SideTies
end
end

