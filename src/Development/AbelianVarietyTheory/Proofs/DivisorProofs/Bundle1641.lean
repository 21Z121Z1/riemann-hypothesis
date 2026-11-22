import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0253
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0702
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0794
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0730
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0793
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0723
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PairingMulFirstChern
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1612
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIsoCompatibleLocalLanglandsThree
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LawsTTransport

open GlobalTheory.LocLanglands.FieldCompat GlobalTheory.LocLanglands.TransportGL

theorem lawsA_transport : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h'), (∀ x x', RepRel i x x' → WDRel (RingEquiv.refl Ω) (rc x) (rc' x')) → ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a), UpperTheory.Zero.LLC.LawsT a ha rc → ∀ (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a'), (∀ x, (rc' x).lpDim = x.1) ∧ (∀ χ hχ, rc' (.ofChar χ hχ) = WD.lpOfChar h' (χ.comp a') (ha'.smooth hχ)) ∧ (∀ (l : List (Segment (w'.adicCompletion E'))) (x : IrrGL (w'.adicCompletion E')), IsL (l : Multiset (Segment (w'.adicCompletion E'))) x.rep → rc' x = segSum rc' l) ∧ (∀ x, x.IsCusp → IsIrrWD (rc' x)) ∧ (∀ x (s : ℝ), rc' (x.nu s) = (rc' x).lpTw s) := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ A w w' h h' j i P rc rc' hR a ha L a' ha'
  have hG := GlobalTheory.globalArtinReciprocity_holds
  have hC := GlobalTheory.Published.chevalleyUnits'
  have h3 := P.cont
  have := charZero_compl w
  have := charZero_compl w'
  have hs : Continuous i.symm := (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation _ _ i h3).1
  obtain ⟨T, hT, hTd⟩ := GlobalTheory.T.transportIrrGL_bijective_degree_charZero _ _ i h3
  obtain ⟨hcu, hch⟩ := GlobalTheory.T.transport_keeps_cuspidal_twists_characters _ _ i h3
  obtain ⟨S, hS, hSd, hS0, hSs, hSc, hSt, hSp, hSi, hSo⟩ :=
    GlobalTheory.T.place_over_transport_ring_iso_symm E Ω A w h E' Ω A w' h' (RingEquiv.refl Ω) j i P
  have hart := GlobalTheory.T.localArtinMap_unique_transport_placeIso hG hC E Ω A w h E' Ω A w' h' (RingEquiv.refl Ω) j i P a a' ha ha'
  have hrel : ∀ x', RepRel i (T.symm x') x' := fun x' => (hT _ _).2 (T.apply_symm_apply x')
  have key : ∀ x', rc' x' = S (rc (T.symm x')) := fun x' => ((hS _ _).1 (hR _ _ (hrel x'))).symm
  have hcusp : ∀ x', (T.symm x').IsCusp ↔ x'.IsCusp := fun x' => (hcu _ _ (hrel x')).1
  refine ⟨fun x' => ?_, fun χ' hχ' => ?_, fun l x' hx => ?_, fun x' hx => ?_, fun x' s => ?_⟩
  · rw [key, hSd, L.dim, ← hTd, T.apply_symm_apply]
  · have hχ := isSmoothChar_comp i h3 hχ'
    have R := hch _ hχ χ' hχ' (fun _ => rfl)
    rw [key, ← (hT _ _).1 R, T.symm_apply_apply, L.one]
    refine hSo _ _ _ _ fun σ σ' hσ => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, hart σ σ' hσ]
  · let f : Segment (w'.adicCompletion E') → Segment (w.adicCompletion E) := fun Δ =>
      Segment.ofFirst (T.symm Δ.first) ((hcusp _).2 Δ.isCusp_first) Δ.len Δ.len_pos
    have hl := GlobalTheory.T.isLanglandsData_transport_localFieldIso _ _ i.symm hs l (l.map f) x' (T.symm x')
      (by rw [List.forall₂_map_right_iff, List.forall₂_same]; exact fun Δ _ => ⟨repRel_symm (hrel _), rfl⟩)
      (repRel_symm (hrel x')) hx
    rw [key, L.langlands _ _ hl]
    clear hl hx
    induction l with
    | nil => exact hS0
    | cons Δ l ih =>
      simp only [segSum, sumList, List.map_cons, List.foldr_cons] at ih ⊢
      rw [hSs, ih, hSc, hSt, hSp, show (f Δ).first = T.symm Δ.first from rfl,
        show (f Δ).len = Δ.len from rfl, ← key]
  · rw [key, hSi]
    exact L.cusp _ ((hcusp x').2 hx)
  · have R : RepRel i ((T.symm x').nu s) (x'.nu s) := (hcu _ _ (hrel x')).2 s
    rw [key, ← (hT _ _).1 R, T.symm_apply_apply, L.nu, hSt, ← key]

end GlobalTheory.LawsTTransport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationMixedTermOfPowers
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

namespace GlobalTheory

theorem addMonoidHom_intCast_mul_real {A : Type} [CommRing A] (θ : A →+ ℝ) (k : ℤ) (z : A) :
    θ ((k : A) * z) = (k : ℝ) * θ z := by
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]

theorem polarisation_mixed_term_of_powers : ∀ (A : Type) [CommRing A] (θ : A →+ ℝ) (ι : Type) [Fintype ι] (x : Option ι → A) (D : ℕ) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ), (∀ n : Option ι → ℤ, Φ (lin (fun o => (n o : ℝ)) ^ (D + 1)) = θ ((∑ o, n o • x o) ^ (D + 1))) → ∀ n : ι → ℤ, Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) = θ ((∑ i, n i • x (some i)) ^ D * x none) := by
  intro A _ θ ι _ x D Φ h n
  set Y : MvPolynomial (Option ι) ℝ := MvPolynomial.X none with hY
  set L : MvPolynomial (Option ι) ℝ := rename some (lin fun i => (n i : ℝ)) with hL
  set y : A := ∑ i, n i • x (some i) with hy
  set P : Polynomial ℝ := ∑ a ∈ Finset.range (D + 2),
    Polynomial.C (Φ (Y ^ a * L ^ (D + 1 - a)) * ((D + 1).choose a : ℝ)) * Polynomial.X ^ a with hP
  set Q : Polynomial ℝ := ∑ a ∈ Finset.range (D + 2),
    Polynomial.C (θ (x none ^ a * y ^ (D + 1 - a)) * ((D + 1).choose a : ℝ)) * Polynomial.X ^ a with hQ
  have key : ∀ t : ℤ, P.eval (t : ℝ) = Q.eval (t : ℝ) := by
    intro t
    have ht := h (fun o => Option.elim o t n)
    have hlin : lin (fun o => ((Option.elim o t n : ℤ) : ℝ)) = MvPolynomial.C (t : ℝ) * Y + L := by
      simp only [lin, Fintype.sum_option, Option.elim, hY, hL, map_sum, map_mul, rename_C, rename_X]
    have hsum : (∑ o, (Option.elim o t n) • x o) = (t : A) * x none + y := by
      simp only [Fintype.sum_option, Option.elim, hy, zsmul_eq_mul]
    rw [hlin, hsum, add_pow, add_pow, map_sum, map_sum] at ht
    simp only [hP, hQ, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    have e1 : ∀ a : ℕ, Φ ((MvPolynomial.C (t : ℝ) * Y) ^ a * L ^ (D + 1 - a) * (((D + 1).choose a : ℕ) : MvPolynomial (Option ι) ℝ))
        = Φ (Y ^ a * L ^ (D + 1 - a)) * ((D + 1).choose a : ℝ) * (t : ℝ) ^ a := by
      intro a
      have : (MvPolynomial.C (t : ℝ) * Y) ^ a * L ^ (D + 1 - a) * (((D + 1).choose a : ℕ) : MvPolynomial (Option ι) ℝ)
          = ((t : ℝ) ^ a * ((D + 1).choose a : ℝ)) • (Y ^ a * L ^ (D + 1 - a)) := by
        rw [MvPolynomial.smul_eq_C_mul, map_mul, map_pow, mul_pow, map_natCast]
        ring
      rw [this, map_smul, smul_eq_mul]
      ring
    have e2 : ∀ a : ℕ, θ (((t : A) * x none) ^ a * y ^ (D + 1 - a) * (((D + 1).choose a : ℕ) : A))
        = θ (x none ^ a * y ^ (D + 1 - a)) * ((D + 1).choose a : ℝ) * (t : ℝ) ^ a := by
      intro a
      have : ((t : A) * x none) ^ a * y ^ (D + 1 - a) * (((D + 1).choose a : ℕ) : A)
          = (((t ^ a * ((D + 1).choose a : ℤ)) : ℤ) : A) * (x none ^ a * y ^ (D + 1 - a)) := by
        push_cast
        ring
      rw [this, addMonoidHom_intCast_mul_real]
      push_cast
      ring
    simp only [e1, e2] at ht
    exact ht
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := Set.range (fun t : ℤ => (t : ℝ)))
    · rintro _ ⟨t, rfl⟩
      exact key t
    · exact Set.infinite_range_of_injective Int.cast_injective
  have hc := congrArg (fun p => Polynomial.coeff p 1) hPQ
  simp only [hP, hQ, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow] at hc
  simp only [Finset.sum_ite_eq, Finset.mem_range] at hc
  rw [if_pos (by omega), if_pos (by omega)] at hc
  · simp only [pow_one, Nat.choose_one_right, Nat.add_sub_cancel] at hc
    have hD : ((D + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast at hc hD
    have := mul_right_cancel₀ hD hc
    rw [mul_comm (y ^ D)]
    exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceFixedVectorsNeBotTransport
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.KOneTransport

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

def intMap (i : k ≃+* k') (hv : ∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) : 𝒪[k] →+* 𝒪[k'] :=
  (i.toRingHom.comp (𝒪[k]).subtype).codRestrict 𝒪[k'] fun x => (hv x).2 x.2

theorem intMap_coe (i : k ≃+* k') (hv : ∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) (x : 𝒪[k]) :
    ((intMap i hv x : 𝒪[k']) : k') = i x := rfl

theorem symm_hv (i : k ≃+* k') (hv : ∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) :
    ∀ y : k', valuation k (i.symm y) ≤ 1 ↔ valuation k' y ≤ 1 := fun y => by
  have := hv (i.symm y); rw [RingEquiv.apply_symm_apply] at this; exact this.symm

theorem isLocalHom_intMap (i : k ≃+* k') (hv : ∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) :
    IsLocalHom (intMap i hv) := by
  refine ⟨fun a ha => ?_⟩
  have h := ha.map (intMap i.symm (symm_hv i hv))
  have e : intMap i.symm (symm_hv i hv) (intMap i hv a) = a := Subtype.ext (by
    rw [intMap_coe, intMap_coe, RingEquiv.symm_apply_apply])
  rwa [e] at h

theorem map_mem_kOne (i : k ≃+* k') (hv : ∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) {n : ℕ}
    {g : GL (Fin n) k} (hg : g ∈ GlobalTheory.SplitWeil.KOne k (Fin n)) :
    GeneralLinearGroup.map i.toRingHom g ∈ GlobalTheory.SplitWeil.KOne k' (Fin n) := by
  haveI := isLocalHom_intMap i hv
  obtain ⟨g0, hg0, rfl⟩ := Subgroup.mem_map.1 hg
  refine Subgroup.mem_map.2 ⟨GeneralLinearGroup.map (intMap i hv) g0, ?_, ?_⟩
  · rw [MonoidHom.mem_ker] at hg0 ⊢
    ext a b
    have h := congrArg (fun m : GL (Fin n) (IsLocalRing.ResidueField 𝒪[k]) => (m.val : Matrix (Fin n) (Fin n) _) a b) hg0
    simp only [GeneralLinearGroup.map_apply, Units.val_one] at h ⊢
    rw [← IsLocalRing.ResidueField.map_residue, h]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  · ext a b
    simp [GeneralLinearGroup.map_apply]
    rfl

end GlobalTheory.KOneTransport

open GlobalTheory.LocLanglands.FieldCompat GlobalTheory.LocLanglands.TransportGL in

theorem GlobalTheory.KOneTransport.fixed_ne_bot_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (x : IrrGL k) (x' : IrrGL k'), RepRel i x x' → GlobalTheory.PRep.fixed x.rep (GlobalTheory.SplitWeil.KOne k (Fin x.1)) ≠ ⊥ → GlobalTheory.PRep.fixed x'.rep (GlobalTheory.SplitWeil.KOne k' (Fin x'.1)) ≠ ⊥ := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi x x' H hx
  obtain ⟨-, hv, -⟩ := GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k k' i hi
  rw [← cls_rep x] at H
  obtain ⟨π', e, rfl, he⟩ := GlobalTheory.TheRecTransport.exists_of_repRel _ H
  obtain ⟨v, hv0, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hx
  let φ := equivRep π'
  have h2 : ∀ g v, φ.toLinearEquiv (π'.ρ g v) = π'.cl.rep.ρ g (φ.toLinearEquiv v) := fun g v =>
    φ.toIntertwiningMap.isIntertwining _ _ g v
  rw [Submodule.ne_bot_iff]
  refine ⟨φ.toLinearEquiv (e v), fun h => ?_, ?_⟩
  · have hg : GeneralLinearGroup.map i.symm.toRingHom (h : GL (Fin x.1) k') ∈ GlobalTheory.SplitWeil.KOne k (Fin x.1) :=
      GlobalTheory.KOneTransport.map_mem_kOne i.symm (GlobalTheory.KOneTransport.symm_hv i hv) h.2
    have hfx : x.rep (GeneralLinearGroup.map i.symm.toRingHom (h : GL (Fin x.1) k')) v = v := by
      have := hv0 ⟨_, hg⟩
      simpa using this
    have h3 := he (GeneralLinearGroup.map i.symm.toRingHom (h : GL (Fin x.1) k')) v
    rw [map_map_symm] at h3
    show π'.cl.rep.ρ (h : GL (Fin x.1) k') (φ.toLinearEquiv (e v)) = ((1 : _ →* ℂˣ) h : ℂ) • φ.toLinearEquiv (e v)
    rw [← h2, ← h3]
    erw [hfx]
    simp
  · intro h0
    apply hvne
    have : e v = 0 := φ.toLinearEquiv.map_eq_zero_iff.1 h0
    exact e.map_eq_zero_iff.1 this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineChartFamiliesAgreeOnOverlap
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LineConst

noncomputable section

namespace GlobalTheory.LineConst
open Polynomial

variable {k : Type} [Field k]

private theorem scaleX_isUnit (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    IsUnit ((algebraMap (Polynomial R) (Localization.Away (X : Polynomial R))).comp (scaleHom k R u) X) := by
  simp only [RingHom.comp_apply, scaleHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_mul]
  refine IsUnit.mul ?_ (IsLocalization.Away.algebraMap_isUnit _)
  exact ((isUnit_iff_exists_inv.mpr ⟨v, huv⟩).map Polynomial.C).map _

private def psiHom (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    Localization.Away (X : Polynomial k) →+* Localization.Away (X : Polynomial R) :=
  IsLocalization.Away.lift (X : Polynomial k) (scaleX_isUnit R huv)

private theorem psi_loc (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    (algebraMap (Polynomial R) (Localization.Away (X : Polynomial R))).comp (scaleHom k R u) =
      (psiHom R huv).comp (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k))) :=
  RingHom.ext fun a => by simp only [RingHom.comp_apply, psiHom, IsLocalization.Away.lift_eq]

private theorem psi_inv (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    (Polynomial.aeval (IsLocalization.Away.invSelf (X : Polynomial R) :
        Localization.Away (X : Polynomial R))).toRingHom.comp (scaleHom k R v) =
      (psiHom R huv).comp (Polynomial.aeval (IsLocalization.Away.invSelf (X : Polynomial k) :
        Localization.Away (X : Polynomial k))).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    have e : (algebraMap k (Localization.Away (X : Polynomial k))) a =
        algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) (Polynomial.C a) := by
      rw [IsScalarTower.algebraMap_apply k (Polynomial k) (Localization.Away (X : Polynomial k))]
      rfl
    have e2 : (algebraMap R (Localization.Away (X : Polynomial R))) (algebraMap k R a) =
        algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) (Polynomial.C (algebraMap k R a)) := by
      rw [IsScalarTower.algebraMap_apply R (Polynomial R) (Localization.Away (X : Polynomial R))]
      rfl
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C, e, psiHom,
      IsLocalization.Away.lift_eq]
    simp [scaleHom, e2]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X]
    have hb : psiHom R huv (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X) =
        algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) (Polynomial.C u) *
          algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) X := by
      simp [psiHom, IsLocalization.Away.lift_eq, scaleHom]
    have hc : psiHom R huv (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X) *
        psiHom R huv (IsLocalization.Away.invSelf (X : Polynomial k) : Localization.Away (X : Polynomial k)) = 1 := by
      rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    have hl : (Polynomial.aeval (IsLocalization.Away.invSelf (X : Polynomial R) :
        Localization.Away (X : Polynomial R))) (scaleHom k R v X) *
        psiHom R huv (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X) = 1 := by
      rw [hb]
      have hv : (Polynomial.aeval (IsLocalization.Away.invSelf (X : Polynomial R) :
          Localization.Away (X : Polynomial R))) (scaleHom k R v X) =
          algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) (Polynomial.C v) *
            IsLocalization.Away.invSelf (X : Polynomial R) := by
        simp [scaleHom, Polynomial.aeval_def, Polynomial.eval₂_mul]
        congr 1
      rw [hv]
      calc _ = algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) (Polynomial.C (v * u)) *
            (algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) X *
              IsLocalization.Away.invSelf (X : Polynomial R)) := by rw [map_mul, map_mul]; ring
        _ = 1 := by rw [IsLocalization.Away.mul_invSelf, mul_comm v u, huv, map_one, map_one, _root_.one_mul]
    exact left_inv_eq_right_inv hl hc

private theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

private theorem scaled_loc (B : Over (Sp k)) (f₀ f₁ : Sp (Polynomial k) ⟶ B.left)
    (h0 : f₀ ≫ B.hom = spMap (algebraMap k (Polynomial k)))
    (h1 : f₁ ≫ B.hom = spMap (algebraMap k (Polynomial k)))
    (hyp : spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) :
        Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁)
    (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ (scaled B f₀ h0 R u).left =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ (scaled B f₁ h1 R v).left := by
  change _ ≫ spMap (scaleHom k R u) ≫ f₀ = _ ≫ spMap (scaleHom k R v) ≫ f₁
  rw [← Category.assoc, ← Category.assoc, sp_comp, sp_comp, psi_loc R huv, psi_inv R huv,
    ← sp_comp (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) (psiHom R huv),
    Category.assoc, hyp, ← Category.assoc, sp_comp]

private def locOver (R : Type) [CommRing R] [Algebra k R] : Over (Sp k) :=
  Over.mk (spMap (algebraMap k (Localization.Away (Polynomial.X : Polynomial R))))

private def locIncl (R : Type) [CommRing R] [Algebra k R] : locOver (k := k) R ⟶ lineOver k R :=
  Over.homMk (spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R)))) (by
    change spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫
      spMap (algebraMap k (Polynomial R)) = spMap (algebraMap k (Localization.Away (Polynomial.X : Polynomial R)))
    rw [sp_comp, ← IsScalarTower.algebraMap_eq])

private def locInv (R : Type) [CommRing R] [Algebra k R] : locOver (k := k) R ⟶ lineOver k R :=
  Over.homMk (spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
      Localization.Away (Polynomial.X : Polynomial R))).toRingHom) (by
    change spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
      Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫
      spMap (algebraMap k (Polynomial R)) = spMap (algebraMap k (Localization.Away (Polynomial.X : Polynomial R)))
    have e : (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom.comp (algebraMap k (Polynomial R)) =
        algebraMap k (Localization.Away (Polynomial.X : Polynomial R)) := by
      refine RingHom.ext fun a => ?_
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.algebraMap_apply,
        Polynomial.aeval_C]
      exact (IsScalarTower.algebraMap_apply k R (Localization.Away (Polynomial.X : Polynomial R)) a).symm
    rw [sp_comp, e])

theorem famMap_loc_eq : ∀ {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f₀ f₁ : Sp (Polynomial k) ⟶ B.left) (h0 : f₀ ≫ B.hom = spMap (algebraMap k (Polynomial k))) (h1 : f₁ ≫ B.hom = spMap (algebraMap k (Polynomial k))), spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) : Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁ → ∀ (R : Type) [CommRing R] [Algebra k R] (u v : R), u * v = 1 → spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ famMap B f₀ h0 R u = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) : Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ famMap B f₁ h1 R v := by
  intro k _ B _ f₀ f₁ h0 h1 hyp R _ _ u v huv
  have hs : ∀ {a b : R}, a * b = 1 → locIncl (k := k) R ≫ scaled B f₀ h0 R a = locInv R ≫ scaled B f₁ h1 R b := by
    intro a b hab
    ext1
    exact scaled_loc B f₀ f₁ h0 h1 hyp R hab
  have h := congrArg CommaMorphism.left
    (show locIncl (k := k) R ≫ (scaled B f₀ h0 R u * (scaled B f₀ h0 R 1)⁻¹) =
        locInv R ≫ (scaled B f₁ h1 R v * (scaled B f₁ h1 R 1)⁻¹) by
      rw [MonObj.comp_mul, GrpObj.comp_inv, MonObj.comp_mul, GrpObj.comp_inv, hs huv, hs (_root_.one_mul 1)])
  exact h

end GlobalTheory.LineConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOfValuesSesq
section
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

open scoped ComplexConjugate

namespace GlobalTheory.SecForm

theorem coordVec_expand {n : ℕ} (w : V n) : w = ∑ a, w a • coordVec a := by
  ext i
  simp [coordVec, EuclideanSpace.single_apply, Pi.single_apply]

theorem sesq_sum_left {n : ℕ} {α : V n → V n → ℂ} (hα : IsSesq α) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (x : ι → V n) (y : V n) : α (∑ i ∈ s, c i • x i) y = ∑ i ∈ s, c i * α (x i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := hα.smul_left 0 0 y
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hα.add_left, hα.smul_left, ih, smul_eq_mul]

theorem sesq_sum_right {n : ℕ} {α : V n → V n → ℂ} (hα : IsSesq α) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (x : V n) (y : ι → V n) : α x (∑ i ∈ s, c i • y i) = ∑ i ∈ s, conj (c i) * α x (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := hα.smul_right 0 x 0
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hα.add_right, hα.smul_right, ih, smul_eq_mul]

theorem sesq_expand {n : ℕ} {α : V n → V n → ℂ} (hα : IsSesq α) (x y : V n) :
    α x y = ∑ a, ∑ b, α (coordVec a) (coordVec b) * (x a * conj (y b)) := by
  calc α x y = α (∑ a, x a • coordVec a) (∑ b, y b • coordVec b) := by
        rw [← coordVec_expand x, ← coordVec_expand y]
    _ = _ := by
        rw [sesq_sum_left hα]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [sesq_sum_right hα, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring

theorem pull_ofValues : ∀ {n : ℕ} (L : V n →L[ℂ] V n) (α : V n → V n → ℂ), IsSesq α → pull L (ofValues α : Alt n) = ofValues (fun ξ η => α (L ξ) (L η)) := by
  intro n L α hα
  simp only [ofValues, sesq_expand hα (L _), AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, sym, map_sum,
    map_smul, map_mul, (pull_dz L _).1, (pull_dz L _).2, Finset.sum_mul, Finset.mul_sum, Finset.sum_smul,
    Finset.smul_sum, smul_mul_smul_comm, smul_smul]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, c, 2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, c]; rw [Finset.sum_comm]

end GlobalTheory.SecForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PuncturedLineOpenCofiniteStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_compl_punctured_line_open : ∀ (k : Type) [Field k] (V : Set (Sp (Localization.Away (Polynomial.X : Polynomial k)))), IsOpen V → ∀ (χ₁ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k), spMap χ₁.toRingHom (IsLocalRing.closedPoint k) ∈ V → Set.Finite {c : k | c ≠ 0 ∧ ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k, χ (algebraMap (Polynomial k) _ Polynomial.X) = c → spMap χ.toRingHom (IsLocalRing.closedPoint k) ∉ V} := by
  first | exact @GlobalTheory.punctured_line_open_cofinite | exact GlobalTheory.punctured_line_open_cofinite | (intros; apply GlobalTheory.punctured_line_open_cofinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientMetricNormProductFormulaStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_metric_norm_product_formula : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (S : ShortComplex X.Modules) (h : Met p σ S.X₂ (1 + 1)) (hS : S.ShortExact) (h₁ : IsVB S.X₁ 1) (h₃ : IsVB S.X₃ 1) (U : X.Opens) (t : Γ(S.X₁, U)) (w : Γ(S.X₂, U)), IsFrame (fun _ : Fin 1 => t) → ∀ y ∈ ptsIn p σ U, ((h.quot hS h₁ h₃).form (S.g.app U w) (S.g.app U w) y).re * (h.form (S.f.app U t) (S.f.app U t) y).re = (h.form w w y).re * (h.form (S.f.app U t) (S.f.app U t) y).re - ‖h.form w (S.f.app U t) y‖ ^ 2 := by
  first | exact @GlobalTheory.CurveDens.quot_form_pyth_rankTwo | exact GlobalTheory.CurveDens.quot_form_pyth_rankTwo | (intros; apply GlobalTheory.CurveDens.quot_form_pyth_rankTwo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDarbouxTransfersHaarFundamentalDomainStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalDarboux_transfers_haar_fundamentalDomain : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ (ν : Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)), ν.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratL T S) 𝓕 ν →
          ∃ (ν' : @Measure ((κ → AF D.host.F) × (κ → AF D.host.F)) (borel _)) (𝓕' : Set ((κ → AF D.host.F) × (κ → AF D.host.F))),
            @Measure.IsAddHaarMeasure _ _ _ (borel _) ν' ∧
            @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) _ _ _ (borel _) 𝓕' ν' ∧
            ∀ f : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ,
              ∫⁻ w in 𝓕, ‖f (co.e w)‖ₑ ^ 2 ∂ν = ∫⁻ w in 𝓕', ‖f w‖ₑ ^ 2 ∂ν' := by
  first | exact @GlobalTheory.RatDarbouxTransfer.haar_fundDomain_transfer | exact GlobalTheory.RatDarbouxTransfer.haar_fundDomain_transfer | (intros; apply GlobalTheory.RatDarbouxTransfer.haar_fundDomain_transfer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealTraceArchimedeanEmbeddingsNondegenerateStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realTrace_archimedeanEmbeddings_nondegenerate : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    IsInfFam θ → ∀ a : Ainf D.host.F, a ≠ 0 →
      ∃ b : Ainf D.host.F, (∑ ρ, θ ρ ((a * b) ⊗ₜ[D.host.F] (1 : D.host.E))).re ≠ 0 := by
  first | exact @GlobalTheory.InfTraceNondeg.realTrace_nondeg | exact GlobalTheory.InfTraceNondeg.realTrace_nondeg | (intros; apply GlobalTheory.InfTraceNondeg.realTrace_nondeg <;> assumption)
end

