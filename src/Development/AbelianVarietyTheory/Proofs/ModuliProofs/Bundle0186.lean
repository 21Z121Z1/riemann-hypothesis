import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformRegularityBound
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0172
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsHaveFiniteDimensionInvarianceIsomorphism
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardZerosOnTorsionLeOfSymmetricVeryAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotMemBasicOpenOfGeom
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.AwayLiftCompFromZeroRingHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdealOfLocally
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PullInvClsOfFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymAndLinearisationOdd
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianVarietyCutOutBoundedDegreeTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

namespace GlobalTheory.TorsionCut

theorem appLE_resG {X X' : Scheme.{0}} (φ : X' ⟶ X) {U V : X.Opens} {U' V' : X'.Opens} (h : V ≤ U) (h' : V' ≤ U')
    (a : U' ≤ φ ⁻¹ᵁ U) (b : V' ≤ φ ⁻¹ᵁ V) (f : Γ(X, U)) :
    (φ.appLE V V' b).hom (resG X h f) = resG X' h' ((φ.appLE U U' a).hom f) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem appLE_surjective {X X' : Scheme.{0}} (φ : X' ⟶ X) [IsIso φ] {U : X.Opens} {U' : X'.Opens}
    (h : U' = φ ⁻¹ᵁ U) : Function.Surjective (φ.appLE U U' h.le).hom := by
  subst h
  rw [Scheme.Hom.appLE_eq_app]
  exact (ConcreteCategory.bijective_of_isIso (φ.app U)).2

theorem vamp_pull {K σ : Type} [Field K] {X X' : Scheme.{0}} (φ : X' ⟶ X) [IsIso φ] (p : X ⟶ Sp K) (M : LB X)
    (th : σ → M.Sec) (h : VAmp p M th) : VAmp (φ ≫ p) (M.pull φ) fun i => secPull (th i) φ := by
  refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
  · simp only [nonzeroLocus_secPull]
    rw [← Scheme.Hom.preimage_iSup, h.1]; rfl
  · rw [nonzeroLocus_secPull]
    exact (h.2 i).1.preimage φ
  · obtain ⟨r, hr, hs⟩ := (h.2 i).2
    have hD := nonzeroLocus_secPull (th i) φ
    refine ⟨fun j => (φ.appLE _ _ hD.le).hom (r j), fun j k => ?_, fun f => ?_⟩
    · have hk : (M.pull φ).U k ≤ φ ⁻¹ᵁ M.U (k PUnit.unit) := LB.wchart_le M (fun _ : PUnit => φ) k PUnit.unit
      have e := congrArg (φ.appLE (Out.nonzeroLocus (th i) ⊓ M.U (k PUnit.unit))
        (Out.nonzeroLocus (secPull (th i) φ) ⊓ (M.pull φ).U k) (inf_le_inf hD.le hk)).hom (hr j (k PUnit.unit))
      rw [map_mul] at e
      exact (appLE_resG φ _ inf_le_right hk _ _).symm.trans (e.trans (congrArg₂ (· * ·)
        (appLE_resG φ _ inf_le_left hD.le _ _) (appLE_resG φ _ inf_le_right hk _ _)))
    · obtain ⟨f, rfl⟩ := appLE_surjective φ hD f
      obtain ⟨F, rfl⟩ := hs f
      refine ⟨F, ?_⟩
      rw [MvPolynomial.eval₂_comp_left, ← RingHom.comp_assoc, ← CommRingCat.hom_comp]
      erw [Scheme.Hom.appLE_comp_appLE]
      rfl

theorem vamp_of_comp {K σ σ₀ : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) (M : LB X) (th : σ₀ → M.Sec)
    (r : σ → σ₀) (hr : Function.Surjective r) (h : VAmp p M (th ∘ r)) : VAmp p M th := by
  obtain ⟨s, hs⟩ := hr.hasRightInverse
  refine ⟨?_, fun i => ?_⟩
  · rw [← h.1]; exact (hr.iSup_comp fun i => Out.nonzeroLocus (th i)).symm
  · obtain ⟨i, rfl⟩ := hr i
    obtain ⟨ha, ρ, h₁, h₂⟩ := h.2 i
    refine ⟨ha, ρ ∘ s, fun j k => ?_, fun f => ?_⟩
    · have := h₁ (s j) k
      simp only [Function.comp_apply, hs j] at this
      exact this
    · obtain ⟨F, rfl⟩ := h₂ f
      refine ⟨MvPolynomial.rename r F, ?_⟩
      rw [MvPolynomial.eval₂_rename]
      congr 1
      funext a
      refine fn_ext fun y hy => ?_
      obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hy
      have hy' : y ∈ Out.nonzeroLocus (th (r i)) ⊓ M.U k := ⟨hy, hk⟩
      have e₁ := congrArg (gs (𝟙 X) y _) (h₁ a k)
      have e₂ := congrArg (gs (𝟙 X) y _) (h₁ (s (r a)) k)
      simp only [Function.comp_apply, hs (r a)] at e₁ e₂ ⊢
      rw [gs_mul _ y _ hy', gs_res _ y _ hy', gs_res _ y _ hy', gs_res _ y _ hy'] at e₁ e₂
      exact ((mem_nonzeroLocus_iff_isUnit _ hk).1 hy).mul_right_cancel (e₁.symm.trans e₂)

theorem secCoord_comp {σ σ₀ : Type} {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) (th : σ₀ → M.Sec)
    (r : σ → σ₀) (s : σ₀ → σ) (hs : ∀ a, r (s a) = a) {R : Type} [CommRing R] (x : Sp R ⟶ X) (v : σ → R)
    (h : SecCoord M (th ∘ r) x v) : SecCoord M th x (v ∘ s) ∧ v ∘ s ∘ r = v := by
  obtain ⟨τ, hτ, h⟩ := h
  refine ⟨⟨τ, hτ, fun i j hj => ?_⟩, funext fun a => ?_⟩
  · have := h (s i) j hj
    simp only [Function.comp_apply, hs i] at this
    exact this
  · apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1
    refine (Sp R).IsSheaf.section_ext fun y _ => ?_
    obtain ⟨k, hk⟩ := exists_chart hM (x y)
    have hj := LB.wchart_le M (fun _ : PUnit => x) (fun _ => k) PUnit.unit
    refine ⟨(M.pull x).U fun _ => k, le_top, mem_pull.2 hk, ?_⟩
    have h₁ := h a (fun _ => k) hj
    have h₂ := h (s (r a)) (fun _ => k) hj
    simp only [Function.comp_apply, hs] at h₁ h₂
    exact (Units.mul_left_inj (τ.s fun _ => k)).1 (h₂.symm.trans h₁)

theorem idealOf_comp {K σ σ₀ : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Sp K) {M : LB X} (hM : M.IsLB)
    (th : σ₀ → M.Sec) (r : σ → σ₀) (hr : Function.Surjective r) :
    idealOf p M (th ∘ r) (𝟙 X) = (idealOf p M th (𝟙 X)).comap (MvPolynomial.rename r) := by
  obtain ⟨s, hs⟩ := hr.hasRightInverse
  ext F
  simp only [idealOf, Ideal.mem_comap, Ideal.mem_iInf, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_rename]
  refine ⟨fun H R _ β y v hv => H R _ β y _ ⟨hv.1, ?_⟩, fun H R _ β y v hv => ?_⟩
  · obtain ⟨τ, hτ, h⟩ := hv.2
    exact ⟨τ, hτ, fun i => h (r i)⟩
  · obtain ⟨h₁, h₂⟩ := secCoord_comp hM th r s hs _ v hv.2
    have := H R _ β y _ ⟨hv.1, h₁⟩
    rwa [Function.comp_assoc, h₂] at this

theorem isDominant_one {K : Type} [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (hg : P.g = 0) :
    IsDominant (1 : Out.baseOver (Sp K) ⟶ P.A).left := by
  have := polAV_isIntegral_of_isAlgClosed K P
  have : Etale P.A.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 (hg ▸ P.smoothDim)
  let e : Sp K ⟶ P.A.left := (1 : Out.baseOver (Sp K) ⟶ P.A).left
  have := isOpenImmersion_of_section_of_etale P.A.hom e (Over.w _)
  exact ⟨e.isOpenEmbedding.isOpen_range.dense ⟨_, (default : PrimeSpectrum K), rfl⟩⟩

theorem sec_eq_zero (h : Out.Laws) (h₂ : Out.Laws2) {K : Type} [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K))
    {Y : Scheme.{0}} (e : Y ≅ P.A.left) (M : LB Y) {σ : Type} [Finite σ] (th : σ → M.Sec) {C d k δ : ℕ}
    (hM : M.IsLB) (hs : SymB (A := P.A) (M.pull e.inv)) (hv : VAmp (e.hom ≫ P.A.hom) M th) (hδ : δ ≤ C ^ P.g)
    (h0 : ∀ n ≥ 1, SectionsHaveFiniteDimension (e.hom ≫ P.A.hom) (lbPow M n) (δ * n ^ P.g)) (hk : C ^ P.g * P.g.factorial * d < k)
    (hK : (k : K) ≠ 0) (τ : (lbPow M d).Sec)
    (hτ : ∀ x : Out.baseOver (Sp K) ⟶ P.A, x ^ k = 1 → ¬ ⊤ ≤ (x.left ≫ e.inv) ⁻¹ᵁ Out.nonzeroLocus τ) (j) :
    τ.f j = 0 := by
  have := polAV_isIntegral_of_isAlgClosed K P
  have : IsReduced Y := isReduced_of_isOpenImmersion e.hom
  by_contra hne
  obtain ⟨z, hz⟩ : ∃ z : P.A.left, z ∈ e.inv ⁻¹ᵁ Out.nonzeroLocus τ := by
    have hb : (Y.basicOpen (τ.f j) : Set Y).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      exact fun h => hne ((basicOpen_eq_bot_iff _).1 (TopologicalSpace.Opens.ext h))
    obtain ⟨y, hy⟩ := hb
    obtain ⟨z, rfl⟩ := e.inv.homeomorph.surjective y
    exact ⟨z, basicOpen_le_nonzeroLocus τ j hy⟩
  rcases Nat.eq_zero_or_pos P.g with hg | hg
  · obtain ⟨y, hy⟩ := (isDominant_one P hg).denseRange.exists_mem_open (TopologicalSpace.Opens.isOpen _) ⟨z, hz⟩
    refine hτ 1 (one_pow _) fun y' _ => ?_
    have : y' = y := Subsingleton.elim (α := PrimeSpectrum K) _ _
    subst this
    exact hy
  have hk1 : 1 ≤ k := by omega
  have hcard : Nat.card {b : Out.baseOver (Sp K) ⟶ P.A // b ^ k = 1} = k ^ (2 * P.g) :=
    (h.mulN (Sp K) P k hk1).2.2.2.2 K (𝟙 _) hK
  have hM' : (M.pull e.inv).IsLB := LB.isLB_linComb hM _ _
  have hv' := vamp_pull e.inv _ M th hv
  rw [e.inv_hom_id_assoc] at hv'
  have H := GlobalTheory.card_zeros_on_torsion_le_of_symmetric_veryAmple h h₂ K P (M.pull e.inv) σ _ C d k hM' hs hv' (fun n hn => ⟨δ * n ^ P.g,
    by rw [mul_pow]; exact Nat.mul_le_mul_right _ hδ, by
      have hn' : (lbPow M n).IsLB := LB.isLB_linComb hM _ _
      have a := ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K Y _ _ hn').2.2.2.2.2 _ e.symm _).1 (h0 n hn)
      rw [Iso.symm_hom, e.inv_hom_id_assoc] at a
      exact ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ P.A.hom _ (LB.isLB_linComb hn' _ _)).2.1 _ (LB.isLB_linComb hM' _ _)
        ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K Y (e.hom ≫ P.A.hom) M hM).2.2.2.2.1 _ e.inv n).symm).1 _ a⟩) hg hK (secPowPull τ e.inv) (by
      rw [← nonzeroLocus_secPowPull] at hz
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
      exact ⟨i, fun e => by rw [e, Scheme.basicOpen_zero] at hi; exact hi⟩)
  rw [nonzeroLocus_secPowPull, Nat.card_congr (Equiv.subtypeEquivRight (q := fun b => b ^ k = 1)
    fun x => ⟨fun a => a.1, fun a => ⟨a, hτ x a⟩⟩), hcard,
    show k ^ (2 * P.g) = k ^ 2 * k ^ (2 * P.g - 2) by rw [← pow_add]; congr 1; omega] at H
  have := Nat.le_of_mul_le_mul_right H (by positivity)
  nlinarith

end GlobalTheory.TorsionCut

namespace GlobalTheory

open TorsionCut in

theorem cutBy_idealOf_torsion : Out.Laws → Out.Laws2 → ∀ (g C : ℕ) (σ₀ : Type) [Finite σ₀] [Nonempty σ₀], ∃ d k₀ : ℕ, ∀ δ ≤ C ^ g, ∀ (σ : Type) [Finite σ] (r : σ → σ₀), Function.Surjective r → ∃ Q : Polynomial ℚ, ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), P.g = g → ∀ (Y : Scheme.{0}) (e : Y ≅ P.A.left) (M : LB Y) (th : σ → M.Sec) (k : ℕ) (Hh : Type) (y : Hh → (Out.baseOver (Sp K) ⟶ P.A)) (p : Hh → σ → K), M.IsLB → SymB (A := P.A) (M.pull e.inv) → VAmp (e.hom ≫ P.A.hom) M th → (∀ a a', r a = r a' → ∀ j, (th a).f j = (th a').f j) → (∀ n ≥ 1, SectionsHaveFiniteDimension (e.hom ≫ P.A.hom) (lbPow M n) (δ * n ^ g)) → k₀ ≤ k → (k : K) ≠ 0 → (∀ x : Out.baseOver (Sp K) ⟶ P.A, x ^ k = 1 → ∃ h, y h = x) → (∀ h, SecCoord M th ((y h).left ≫ e.inv) (p h)) → CutBy (idealOf (e.hom ≫ P.A.hom) M th (𝟙 Y)) Q d p := by
  intro h h₂ g C σ₀ _ _
  obtain ⟨Q₀, hQ₀⟩ := GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule σ₀
  choose d₀ hd₀ using fun δ : ℕ =>
    exists_uniform_regularity_bound σ₀ (Q₀ - Polynomial.C (δ : ℚ) * Polynomial.X ^ g)
  let d := (Finset.range (C ^ g + 1)).sup d₀ + 1
  refine ⟨d, C ^ g * g.factorial * d + 1, fun δ hδ σ _ r hr => ?_⟩
  have hd : d₀ δ ≤ d := (Finset.le_sup (f := d₀) (Finset.mem_range.2 (Nat.lt_succ_of_le hδ))).trans (Nat.le_succ _)
  obtain ⟨Q, hQ⟩ := regularity_comap_rename_of_surjective σ σ₀ r (Q₀ - Polynomial.C (δ : ℚ) * Polynomial.X ^ g) hr
  refine ⟨Q, fun K _ _ P hg Y e M th k Hh y p hM hs hv hth h0 hk hK hy hp => ?_⟩
  subst hg
  obtain ⟨th₀, rfl⟩ : ∃ th₀ : σ₀ → M.Sec, th = th₀ ∘ r := by
    obtain ⟨s, hs⟩ := hr.hasRightInverse
    refine ⟨th ∘ s, funext fun a => ?_⟩
    have := funext (hth a (s (r a)) (hs _).symm)
    change th a = th (s (r a))
    generalize th a = u at this
    generalize th (s (r a)) = v at this
    cases u; cases v; cases this; rfl
  have hv₀ := vamp_of_comp _ M th₀ r hr hv
  obtain ⟨a₁, a₂, -⟩ := GlobalTheory.ZV.FormSec.ideal_of_veryAmple K σ₀ Y _ M th₀ hM hv₀
  obtain ⟨_, a₃⟩ := GlobalTheory.ZV.HilbFn.hilbertFunction_idealOf K σ₀ Y _ M th₀ hM hv₀
  have hreg := hd₀ δ K _ a₁ a₂ (by
    filter_upwards [a₃, Filter.eventually_ge_atTop 1] with n ⟨m, hm, _, hm'⟩ hn
    obtain rfl := (GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K Y _ _ (LB.isLB_linComb hM _ _)).1 _ _ hm (h0 n hn)
    have := congrArg (Nat.cast : ℕ → ℚ) hm'
    rw [hQ₀] at this
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    push_cast at this
    rw [← this, dimDeg]
    ring)
  have hyp : ∀ i, ((y i).left ≫ e.inv) ≫ e.hom ≫ P.A.hom = 𝟙 _ := fun i => by
    rw [Category.assoc, e.inv_hom_id_assoc]; exact Over.w _
  refine cutBy_of_regular_of_zeroEstimate K σ Hh _ Q d d p le_rfl (fun n hn => ?_) (fun F hF i => ?_)
    fun F hF hz => ?_
  · obtain ⟨b₁, b₂⟩ := hQ K _ _ d (idealOf_comp (e.hom ≫ P.A.hom) hM th₀ r hr) (Nat.le_add_left _ _) n hn
    refine ⟨b₁ (hreg n (hd.trans hn)).1, b₂ fun F hF hFn => ?_⟩
    have h := homogeneousComponent_mul_mem_span_degree _ hd hn ((hreg n (hd.trans hn)).2 F hF hFn) 1
    rwa [_root_.one_mul, MvPolynomial.homogeneousComponent_of_mem hFn, if_pos rfl] at h
  · simp only [idealOf, Ideal.mem_iInf, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom] at hF
    exact hF K _ (RingHom.id K) ((y i).left ≫ e.inv) (p i)
      ⟨(hyp i).trans (Spec.map_id _).symm, by rw [Category.comp_id]; exact hp i⟩
  · obtain ⟨τ, -, c₁, c₂⟩ := (GlobalTheory.ZV.FormSec.ideal_of_veryAmple K σ Y _ M _ hM hv).2.2 d F hF
    refine c₁.1 (sec_eq_zero h h₂ P e M _ hM hs hv hδ h0 hk hK τ fun x hx => ?_)
    obtain ⟨i, rfl⟩ := hy x hx
    exact (c₂ _ _ (hyp i) (hp i)).1 (hz i)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoordsExistsUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZM GlobalTheory.IndefiniteRowSideFullHecke.ThetaCosetLabels

noncomputable section
namespace GlobalTheory.ThetaObjCompare
attribute [local instance] MvPolynomial.gradedAlgebra

section Coords
open MvPolynomial HomogeneousIdeal
variable {σ B R R' : Type} [CommRing B] [CommRing R] [CommRing R'] {y : Sp R ⟶ PJ σ B} {β : B →+* R} {v w : σ → R}

theorem map_irrelevant_iff (β : B →+* R) (v : σ → R) :
    (irrelevant (homogeneousSubmodule σ B)).toIdeal.map (eval₂Hom β v) = ⊤ ↔ Ideal.span (Set.range v) = ⊤ := by
  suffices h : (irrelevant (homogeneousSubmodule σ B)).toIdeal.map (eval₂Hom β v) = Ideal.span (Set.range v) by rw [h]
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun F hF => ?_) (Ideal.span_le.2 ?_)
  · have h0 : homogeneousComponent 0 F = 0 := by
      have := (mem_irrelevant_iff _ F).1 hF
      rwa [GradedRing.proj_apply, ← decomposition.decompose'_apply] at *
    have h1 : F ∈ Ideal.span (Set.range (X : σ → MvPolynomial σ B)) := by
      rw [← Set.image_univ, mem_ideal_span_X_image]
      intro m hm
      by_contra hc
      have : m = 0 := by ext i; by_contra hi; exact hc ⟨i, trivial, hi⟩
      subst this
      rw [homogeneousComponent_zero, map_eq_zero_iff _ (C_injective _ _)] at h0
      exact mem_support_iff.1 hm h0
    refine (Ideal.span_le.2 ?_ : _ ≤ Ideal.comap (eval₂Hom β v) (Ideal.span (Set.range v))) h1
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_comap.2 (by rw [eval₂Hom_X']; exact Ideal.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    rw [← eval₂Hom_X' β v i]
    exact Ideal.mem_map_of_mem _ (mem_irrelevant_of_mem _ one_pos (isHomogeneous_X B i))

theorem hasCoords_iff : HasCoords y β v ↔ ∃ h, y = ProjPoint.ofHom (homogeneousSubmodule σ B) (eval₂Hom β v) h := by
  refine ⟨fun ⟨h, e⟩ => ⟨?_, e⟩, fun ⟨h, e⟩ => ⟨_, e⟩⟩
  have := ProjPoint.map_irrelevant_comp _ h (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
  rwa [← RingHom.comp_assoc, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, RingHom.id_comp] at this

theorem coords_span (h : HasCoords y β v) : Ideal.span (Set.range v) = ⊤ :=
  (map_irrelevant_iff β v).1 (hasCoords_iff.1 h).1

theorem exists_hasCoords (β : B →+* R) (hv : Ideal.span (Set.range v) = ⊤) : ∃ y : Sp R ⟶ PJ σ B, HasCoords y β v :=
  ⟨_, hasCoords_iff.2 ⟨(map_irrelevant_iff β v).2 hv, rfl⟩⟩

theorem coords_eq {y' : Sp R ⟶ PJ σ B} (h : HasCoords y β v) (h' : HasCoords y' β v) : y = y' :=
  h.2.trans h'.2.symm

theorem coords_over (h : HasCoords y β v) :
    y ≫ Proj.toSpecZero _ ≫ spMap (algebraMap B ↥(homogeneousSubmodule σ B 0)) = spMap β := by
  replace h := hasCoords_iff.1 h
  obtain ⟨h, rfl⟩ := h
  rw [← Category.assoc, ProjPoint.ofHom_toSpecZero]
  refine (spMap_comp _ _).trans (congrArg spMap (RingHom.ext fun r => eval₂Hom_C β v r))

theorem coords_baseChange (h : HasCoords y β v) (φ : R →+* R') :
    HasCoords (spMap φ ≫ y) (φ.comp β) fun a => φ (v a) := by
  replace h := hasCoords_iff.1 h
  obtain ⟨h, rfl⟩ := h
  have e := comp_eval₂Hom β v φ
  refine hasCoords_iff.2 ⟨e ▸ ProjPoint.map_irrelevant_comp _ h φ, (ProjPoint.SpecMap_ofHom _ _ h φ).trans ?_⟩
  congr 1

theorem coords_unit_mul (h : HasCoords y β v) (u : Rˣ) : HasCoords y β fun a => u * v a := by
  have hs : Ideal.span (Set.range fun a => u * v a) = ⊤ := by
    rw [_root_.eq_top_iff, ← coords_span h, Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    simpa using Ideal.mul_mem_left (Ideal.span (Set.range fun a => u * v a)) (u⁻¹ : Rˣ) (Ideal.subset_span ⟨a, rfl⟩)
  replace h := hasCoords_iff.1 h
  obtain ⟨h, rfl⟩ := h
  refine hasCoords_iff.2 ⟨(map_irrelevant_iff _ _).2 hs, (ProjPoint.ofHom_eq_of_scale _ h _ (u : R) fun n F hF => ?_).symm⟩
  have hF' : F.IsHomogeneous n := hF
  simp only [coe_eval₂Hom, eval₂_eq, Finset.mul_sum, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [show ∑ i ∈ d.support, d i = n from by
    rw [← hF' (mem_support_iff.1 hd), Finsupp.weight_apply]; simp [Finsupp.sum]]
  ring

theorem coords_minor (h : HasCoords y β v) (h' : HasCoords y β w) {i : σ} (hi : IsUnit (v i)) (a c : σ) :
    v a * w c = v c * w a := by
  replace h := hasCoords_iff.1 h
  obtain ⟨h, rfl⟩ := h
  obtain ⟨h', e⟩ := hasCoords_iff.1 h'
  have hX : X i ∈ homogeneousSubmodule σ B 1 := isHomogeneous_X B i
  have hi₁ : IsUnit (eval₂Hom β v (X i)) := by simpa using hi
  have hi₂ : IsUnit (eval₂Hom β w (X i)) := by
    have := ProjPoint.ofHom_preimage_basicOpen _ _ h' one_pos hX
    rw [← e, ProjPoint.ofHom_preimage_basicOpen _ _ h one_pos hX] at this
    rw [← Ideal.span_singleton_eq_top, ← PrimeSpectrum.zeroLocus_empty_iff_eq_top, PrimeSpectrum.zeroLocus_span,
      ← Set.compl_univ_iff, ← PrimeSpectrum.basicOpen_eq_zeroLocus_compl, ← this,
      PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Set.compl_univ_iff, ← PrimeSpectrum.zeroLocus_span,
      PrimeSpectrum.zeroLocus_empty_iff_eq_top, Ideal.span_singleton_eq_top]
    exact hi₁
  rw [ProjPoint.ofHom_eq_awayι _ _ h one_pos hX hi₁, ProjPoint.ofHom_eq_awayι _ _ h' one_pos hX hi₂, cancel_mono] at e
  have e' := spMap_injective e
  have k₁ := fun a => ProjPoint.awayLift_mk_mul (homogeneousSubmodule σ B) _ hi₁ hX 1 (X a) (isHomogeneous_X B a)
  have k₂ := fun a => ProjPoint.awayLift_mk_mul (homogeneousSubmodule σ B) _ hi₂ hX 1 (X a) (isHomogeneous_X B a)
  simp only [← e', pow_one, eval₂Hom_X'] at k₁ k₂
  rw [← k₁ a, ← k₁ c, ← k₂ a, ← k₂ c]; ring

theorem coords_exists_unit (h : HasCoords y β v) (h' : HasCoords y β w) : ∃ u : Rˣ, ∀ a, v a = u * w a := by
  refine ThetaClosed.exists_unit_of_minors (coords_span h) (coords_span h') fun a c => ?_
  refine SegreCoord.eq_of_away fun q => ?_
  obtain ⟨i, hi⟩ : ∃ i, v i ∉ q.asIdeal := by
    by_contra! hc
    exact q.2.ne_top (top_le_iff.1 (coords_span h ▸ Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hc i)))
  refine ⟨v i, hi, ?_⟩
  simpa only [map_mul] using coords_minor (coords_baseChange h (algebraMap R (Localization.Away (v i))))
    (coords_baseChange h' _) (i := i) (IsLocalization.Away.algebraMap_isUnit _) a c

end Coords

section Terms
variable {g M : ℕ} {I B : Type} [CommRing B] {ζ : Bˣ} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}

theorem isMonHom_mul {G : Over S} [GrpObj G] [IsCommMonObj G] (f h : G ⟶ G) [IsMonHom f] [IsMonHom h] :
    IsMonHom (f * h) where
  one_hom := by rw [MonObj.comp_mul, IsMonHom.one_hom, IsMonHom.one_hom, MonObj.one_eq_one, _root_.mul_one]
  mul_hom := by
    have e : ∀ k : G ⟶ G, [IsMonHom k] → (k ⊗ₘ k) ≫ μ[G] = (fst G G ≫ k) * (snd G G ≫ k) := fun k _ => by
      rw [MonObj.mul_eq_mul, MonObj.comp_mul]
      simp
    rw [MonObj.comp_mul, IsMonHom.mul_hom, IsMonHom.mul_hom, e, e, MonObj.mul_eq_mul, MonObj.comp_mul]
    simp only [← Category.assoc, tensorHom_fst, tensorHom_snd, MonObj.comp_mul]
    exact mul_mul_mul_comm _ _ _ _

theorem isMonHom_ev (X : ThObj g M I ζ s) (t : EndTerm I) : IsMonHom (X.ev t) := by
  letI := X.P.isAb.comm
  induction t with
  | var i => exact X.endo_hom i
  | one => exact inferInstanceAs (IsMonHom (𝟙 _))
  | add t t' h h' => exact isMonHom_mul (X.ev t) (X.ev t')
  | neg t h => exact inferInstanceAs (IsMonHom (X.ev t)⁻¹)
  | mul t t' h h' => exact inferInstanceAs (IsMonHom (X.ev t' ≫ X.ev t))

theorem ev_comm {X' : ThObj g M I ζ s'} {X : ThObj g M I ζ s} {f : S' ⟶ S} {φ : X'.P.A.left ⟶ X.P.A.left}
    (h : IsGrpPullback X'.P.A X.P.A f φ) (he : ∀ i, (X'.endo i).left ≫ φ = φ ≫ (X.endo i).left) (t : EndTerm I) :
    (X'.ev t).left ≫ φ = φ ≫ (X.ev t).left := by
  let Φ : Over.mk (X'.P.A.hom ≫ f) ⟶ X.P.A := Over.homMk φ h.1.w
  suffices H : pushHom h X'.P.A (X'.ev t) = Φ ≫ X.ev t from congrArg (fun z => z.left) H
  induction t with
  | var i => exact Over.OverMorphism.ext (he i)
  | one => exact Over.OverMorphism.ext ((Category.id_comp φ).trans (Category.comp_id φ).symm)
  | add t t' H H' => exact (map_mul _ (X'.ev t) (X'.ev t')).trans (by rw [H, H']; exact (MonObj.comp_mul _ _ _).symm)
  | neg t H => exact (map_inv _ (X'.ev t)).trans (by rw [H]; exact (GrpObj.comp_inv _ _).symm)
  | mul t t' H H' =>
    have e : (X'.ev t).left ≫ φ = φ ≫ (X.ev t).left := congrArg (fun z => z.left) H
    have e' : (X'.ev t').left ≫ φ = φ ≫ (X.ev t').left := congrArg (fun z => z.left) H'
    refine Over.OverMorphism.ext ?_
    show ((X'.ev t').left ≫ (X'.ev t).left) ≫ φ = φ ≫ (X.ev t').left ≫ (X.ev t).left
    rw [Category.assoc, e, ← Category.assoc, e', Category.assoc]

end Terms

end GlobalTheory.ThetaObjCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescended
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.OddDescent

theorem exists_descended : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g m : ℕ) (M : LB A.left) (pt : Fin (2 * g) → (𝟙_ (Over (Sp R)) ⟶ A)), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Odd m → IsUnit (m : R) → M.IsLB → Out.RelAmple A M → (∀ i, pt i ^ m = 1) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ A), y ^ m = 1 → ∃! c : Ix g m, Out.linComb (fun i => toUnit (Over.mk x) ≫ pt i) (fun i => (c i).val) = y) → DenseP {q | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), RingHom.ker x = q ∧ IsGrpPullback Pl.A A (spMap x) φ ∧ LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ)} → ∃ L : LB A.left, L.IsLB ∧ Out.Rigidified A L ∧ Out.Sym A L ∧ Out.RelAmple A L ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), IsGrpPullback Pl.A A (spMap x) φ → LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ) → LBIso Pl.L (L.pull φ) :=
  exists_descended_of GlobalTheory.seesaw_rigidified_of_dense GlobalTheory.sym_and_linearisation_odd
    GlobalTheory.pol_iso_symmetrised_root GlobalTheory.AbLaw.CubeAssembly.cube_gen

end GlobalTheory.OddDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleDeeperLevelCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteEtale_deeper_level_cover : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [Field B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), 1 ≤ D.p + D.q → l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (S₂ : Scheme.{0}) (π : S₂ ⟶ S) (o₂ : Obj D l₂ b₂ (π ≫ s)) (m : SABMap o₂.t o.t π), IsFinite π ∧ Etale π ∧ Surjective π ∧ ((∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (o' : Obj D l₂ b₂ (f ≫ s)) (m' : SABMap o'.t o.t f), (∀ a, (o'.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = f ≫ (o.eta a).left) ∧ (∀ a, (o'.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = f ≫ (o.etaA a).left) → ∃! h : T ⟶ S₂, h ≫ π = f ∧ ∃ u : ObjMap o' o₂ h, u.toSABMap.φ ≫ m.φ = m'.φ := by
  first | exact @GlobalTheory.LevCover.levelCover_closed | exact GlobalTheory.LevCover.levelCover_closed | (intros; apply GlobalTheory.LevCover.levelCover_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientPrincipalTripleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeQuotient_principal_triple : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : SAB H (Sp k)) (g p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ t.G)), 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) → (∀ x ∈ C, x ^ p ^ 2 = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p ^ 2 : ℕ) : ℤ) x y 1) → Nat.card C = p ^ (2 * g) → ∃ (t' : SAB H (Sp k)) (ψ : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧ LBIso (lbPow t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left) := by
  first | exact @GlobalTheory.exists_heckeQuotient_triple_of_laws | exact GlobalTheory.exists_heckeQuotient_triple_of_laws | (intros; apply GlobalTheory.exists_heckeQuotient_triple_of_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelIsometryOfDenseGeometricPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_isometry_of_dense_geometric_points : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A)) (o : Type) [CommRing o] (s : S ⟶ Sp o) (z : o) (κ : Type) (lam : κ → D.La) (pt : κ → (Out.baseOver S ⟶ P.A)) (n m : ℕ), 0 < n → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (β : o →+* K) (ζ : Kˣ) (ev : D.La → (Over.mk x ⟶ P.A)), (n : K) ≠ 0 ∧ p ∈ Set.range x ∧ x ≫ s = spMap β ∧ IsPrimitiveRoot ζ n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a ^ n = 1) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act c) ∧ (∀ a c, Out.WeilIs P.A P.L n (ev a) (ev c) (unitOn (ζ ^ D.EF a c))) ∧ (ζ : K) ^ m = β z ∧ ∀ i, ev (lam i) ^ m = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i} → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : o →+* K), (n : K) ≠ 0 → x ≫ s = spMap β → ∃ (ζ : Kˣ) (ev : D.La → (Over.mk x ⟶ P.A)), IsPrimitiveRoot ζ n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a ^ n = 1) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act c) ∧ (∀ a c, Out.WeilIs P.A P.L n (ev a) (ev c) (unitOn (ζ ^ D.EF a c))) ∧ (ζ : K) ^ m = β z ∧ ∀ i, ev (lam i) ^ m = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i := by
  first | exact @GlobalTheory.exists_levelIsometry_of_dense | exact GlobalTheory.exists_levelIsometry_of_dense | (intros; apply GlobalTheory.exists_levelIsometry_of_dense <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolarisationFormOfLineBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarisationForm_of_lineBundle : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left), M.IsLB → ∃ s : P.A ⟶ P.A, FormIs P M s := by
  first | exact @GlobalTheory.BundleForm.exists_formIs | exact GlobalTheory.BundleForm.exists_formIs | (intros; apply GlobalTheory.BundleForm.exists_formIs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KernelTrivialOfEveryPointCoveredStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelTrivial_of_every_point_covered : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (_ : SABMap t' t f), p ∈ Set.range f ∧ Out.KTriv t'.G t'.PP.L) → Out.KTriv t.G t.PP.L := by
  first | exact @GlobalTheory.KTrivGlob.kTriv_of_forall_point | exact GlobalTheory.KTrivGlob.kTriv_of_forall_point | (intros; apply GlobalTheory.KTrivGlob.kTriv_of_forall_point <;> assumption)
end

