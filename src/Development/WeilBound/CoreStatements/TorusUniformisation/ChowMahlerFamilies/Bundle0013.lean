import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExist
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0030
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0006
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0041

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ChartLatticeFinitelyGenerated
section
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

theorem PositivityTheory.Xgn.chart_lattice_finitely_generated : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (B : ChartBundle O x r (Fin r → Ω)) (c : ι), x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ B.lat c) ∧
      ∀ e ∈ B.lat c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k := by
  intro O _ Ω _ _ ι x r B c hc
  obtain ⟨k, f, cc, hf, hcc, hsum, hb⟩ := B.frame c hc
  choose b _ _ hiff using hb
  have hgen : ∀ l q, ∃ n : ℕ, f l ^ n • b l q ∈ B.lat c := by
    intro l q
    refine (hiff l (b l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
    · by_cases h : q' = q
      · subst h
        simp [Subalgebra.one_mem]
      · simp [Pi.single_apply, h, Subalgebra.zero_mem]
    · simp [Pi.single_apply, ite_smul]
  choose nn hnn using hgen
  obtain ⟨g, hg⟩ : ∃ g : Fin k × Fin r → Fin r → Ω, g = fun p => f p.1 ^ nn p.1 p.2 • b p.1 p.2 :=
    ⟨_, rfl⟩
  have hgmem : ∀ p, g p ∈ B.lat c := by
    intro p
    rw [hg]
    exact hnn _ _
  refine ⟨k * r, fun idx => g (finProdFinEquiv.symm idx), fun idx => hgmem _, ?_⟩
  intro e he
  have hloc : ∀ l, ∃ M : ℕ, ∃ a : Fin r → Ω, (∀ q, a q ∈ chartRing O x c) ∧
      f l ^ M • e = ∑ q, a q • g (l, q) := by
    intro l
    obtain ⟨a, ha, hea⟩ := (hiff l e).1 ⟨0, by simpa using he⟩
    choose N hN using ha
    have hle : ∀ q, N q + nn l q ≤ ∑ q', (N q' + nn l q') := fun q =>
      Finset.single_le_sum (f := fun q' => N q' + nn l q') (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ q)
    refine ⟨∑ q', (N q' + nn l q'), fun q => f l ^ (∑ q', (N q' + nn l q') - nn l q) * a q, ?_, ?_⟩
    · intro q
      have h1 : ∑ q', (N q' + nn l q') - nn l q = (∑ q', (N q' + nn l q') - nn l q - N q) + N q := by
        have := hle q
        omega
      beta_reduce
      rw [h1, pow_add, mul_assoc]
      exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (hf l) _) (hN q)
    · rw [hea, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      simp only [hg]
      rw [smul_smul, smul_smul]
      congr 1
      rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel (by have := hle q; omega)]
  choose M a ha hMa using hloc
  have hP : ∀ l, M l ≤ ∑ l', M l' := fun l =>
    Finset.single_le_sum (f := M) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  have hunit : ∃ d : Fin k → Ω, (∀ l, d l ∈ chartRing O x c) ∧
      ∑ l, d l * f l ^ (∑ l', M l') = 1 := by
    let F : Fin k → chartRing O x c := fun l => ⟨f l, hf l⟩
    have h1 : Ideal.span (Set.range F) = ⊤ := by
      rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
      refine ⟨fun l => ⟨cc l, hcc l⟩, ?_⟩
      apply Subtype.ext
      simpa [F] using hsum
    have h2 := Ideal.span_pow_eq_top _ h1 (∑ l', M l')
    rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at h2
    obtain ⟨d, hd⟩ := h2
    refine ⟨fun l => d l, fun l => (d l).2, ?_⟩
    have := congrArg Subtype.val hd
    simpa [F] using this
  obtain ⟨d, hd, hdsum⟩ := hunit
  have key : e = ∑ p : Fin k × Fin r,
      (d p.1 * f p.1 ^ (∑ l', M l' - M p.1) * a p.1 p.2) • g p := by
    rw [Fintype.sum_prod_type]
    calc e = (∑ l, d l * f l ^ (∑ l', M l')) • e := by rw [hdsum, one_smul]
      _ = ∑ l, d l • (f l ^ (∑ l', M l' - M l) • (f l ^ M l • e)) := by
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [smul_smul, smul_smul, mul_assoc, ← pow_add, Nat.sub_add_cancel (hP l)]
      _ = _ := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [hMa l, Finset.smul_sum, Finset.smul_sum]
          refine Finset.sum_congr rfl (fun q _ => ?_)
          rw [smul_smul, smul_smul]
  refine ⟨fun idx => d (finProdFinEquiv.symm idx).1 *
      f (finProdFinEquiv.symm idx).1 ^ (∑ l', M l' - M (finProdFinEquiv.symm idx).1) *
      a (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2, ?_, ?_⟩
  · intro idx
    exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hd _) (Subalgebra.pow_mem _ (hf _) _)) (ha _ _)
  · exact key.trans (Equiv.sum_comp finProdFinEquiv.symm
      (fun p => (d p.1 * f p.1 ^ (∑ l', M l' - M p.1) * a p.1 p.2) • g p)).symm
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HodgeComponentFlagDegree
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.ComponentDegreeAlt

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {W : Type} [AddCommGroup W] [Module Ω W]

theorem wedge_ne_zero {r : ℕ} {b : Fin r → W} (hb : LinearIndependent Ω b) :
    exteriorPower.ιMulti Ω r b ≠ 0 := by
  have h := (exteriorPower.ιMulti_family_linearIndependent_field (n := r) hb).ne_zero
    (Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin r)).toOrderEmbedding)
  intro h0
  apply h
  simpa [exteriorPower.ιMulti_family] using h0

theorem unit_zpow {p : Cpt ξ} {u : Ω} (hu : unitAt ξ p u) (n : ℤ) : unitAt ξ p (u ^ n) := by
  cases n with
  | ofNat n => simpa using ZUnit.pow hu n
  | negSucc n => rw [zpow_negSucc]; exact ZUnit.inv (ZUnit.pow hu _)

theorem unit_prod {p : Cpt ξ} {I : Type} (s : Finset I) (u : I → Ω) (hu : ∀ i, unitAt ξ p (u i)) :
    unitAt ξ p (∏ i ∈ s, u i) :=
  Finset.prod_induction u (unitAt ξ p) (fun _ _ => ZUnit.mul) ZUnit.one (fun i _ => hu i)

theorem mul_mem_span {p : Cpt ξ} {u : Ω} (hu : u ∈ regAt ξ p) (t : Ω) :
    u * t ∈ Submodule.span (regAt ξ p) {t} :=
  Submodule.mem_span_singleton.2 ⟨⟨u, hu⟩, rfl⟩

theorem span_unit_mul {p : Cpt ξ} {u : Ω} (hu : unitAt ξ p u) (t : Ω) :
    Submodule.span (regAt ξ p) {u * t} = Submodule.span (regAt ξ p) {t} := by
  apply le_antisymm
  · exact (Submodule.span_singleton_le_iff_mem _ _).2 (mul_mem_span hu.2.1 t)
  · refine (Submodule.span_singleton_le_iff_mem _ _).2 ?_
    have := mul_mem_span hu.2.2 (u * t)
    rwa [inv_mul_cancel_left₀ hu.1] at this

theorem exists_gen_wedge {L : Lat ξ W} {r : ℕ} {b₀ : Fin r → W} (hb₀ : LinearIndependent Ω b₀)
    (hFl : L.IsFlagVBOn Set.univ b₀) (p : Cpt ξ) :
    ∃ t : Fin r → Ω, (∀ i, (L.gr b₀ i).IsGenAt p (t i)) ∧
      L.wedge r p = Submodule.span (regAt ξ p) {(∏ i, t i) • exteriorPower.ιMulti Ω r b₀} := by
  obtain ⟨U, hU, b, hbF, hbL⟩ := hFl p trivial
  have hfr : L.IsFrameAt b p := hbL p trivial hU
  choose c hc using FlagDet.exists_diag hbF
  refine ⟨c, fun i => FlagGrGen.gr_isGenAt X Ω ξ W L r b₀ b p i (c i) hb₀ hbF hfr (hc i), ?_⟩
  rw [Lat.wedge_eq_span_of_isFrameAt X Ω ξ W _ r _ p hfr,
    FlagDet.alt_triangular (exteriorPower.ιMulti Ω r (M := W)) b b₀ c hc]

theorem lineLat_eq {A B : Lat ξ W} {p q : ℕ} {a : ⋀[Ω]^p W} {b : ⋀[Ω]^q W} (ha : a ≠ 0) (hb : b ≠ 0)
    {x : Cpt ξ} {α β : Ω} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hA : A.wedge p x = Submodule.span (regAt ξ x) {α • a})
    (hB : B.wedge q x = Submodule.span (regAt ξ x) {β • b}) :
    lineLat A B p q a b x = Submodule.span (regAt ξ x) {α / β} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, ⟨α', β', hα', hβ', hA', hB', hf⟩, rfl⟩
    obtain ⟨u, hu, eu⟩ := ZUnit.exists_of_span_eq (smul_ne_zero hα' ha) (hA'.symm.trans hA)
    obtain ⟨v, hv, ev⟩ := ZUnit.exists_of_span_eq (smul_ne_zero hβ' hb) (hB'.symm.trans hB)
    rw [smul_smul] at eu ev
    have e1 : α' = u * α := smul_left_injective Ω ha eu
    have e2 : β' = v * β := smul_left_injective Ω hb ev
    have e3 : f = β' / α' := by rw [← hf]; field_simp
    have e4 : f⁻¹ = (u * v⁻¹) * (α / β) := by
      have := hu.1
      have := hv.1
      rw [e3, e1, e2]; field_simp
    rw [e4]
    exact mul_mem_span (mul_mem hu.2.1 hv.2.2) _
  · refine (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.subset_span ?_)
    exact ⟨β / α, ⟨α, β, hα, hβ, hA, hB, div_mul_cancel₀ _ hα⟩, (inv_div _ _).symm⟩

theorem tens_unit_eq {Λ : Lat ξ Ω} {p : Cpt ξ} {t : Ω} (ht : Λ.IsGenAt p t) (n : ℤ) :
    Lat.tens (fun _ : Unit => Λ) (fun _ => n) p = Submodule.span (regAt ξ p) {t ^ n} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨u, hu, eu⟩ := ZUnit.exists_of_span_eq (hs ()).1 ((hs ()).2.symm.trans ht.2)
    have e : ∏ i : Unit, s i ^ n = u ^ n * t ^ n := by
      rw [Fintype.prod_unique, ← mul_zpow]
      exact congrArg (· ^ n) eu
    rw [e]
    exact mul_mem_span (unit_zpow hu n).2.1 _
  · refine (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.subset_span ?_)
    exact ⟨fun _ => t, fun _ => ht, by rw [Fintype.prod_unique]⟩

theorem zpow_finsum {a : Ω} (ha : a ≠ 0) {I : Type} (s : Finset I) (n : I → ℤ) :
    a ^ (∑ i ∈ s, n i) = ∏ i ∈ s, a ^ n i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ ha, ih]

end General

theorem prod_root {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {Ω : Type} [Field Ω] (t : ∀ s, Fin (labelRk D s) → Ω) (τ : CMType H) :
    ∏ i : Fin (D.p + D.q), t (HodgeCpt.rootIdx D (τ, i)).1 (HodgeCpt.rootIdx D (τ, i)).2 ^
      HodgeCpt.rootSgn D (τ, i) = (∏ i, t (.inl τ) i) / ∏ j, t (.inr τ) j := by
  rw [Fin.prod_univ_add, div_eq_mul_inv]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have h : ((Fin.castAdd D.q i : Fin (D.p + D.q)) : ℕ) < D.p := i.2
    have e : HodgeCpt.rootIdx D (τ, Fin.castAdd D.q i) = ⟨.inl τ, i⟩ := dif_pos h
    have e' : HodgeCpt.rootSgn D (τ, Fin.castAdd D.q i) = 1 := if_pos h
    rw [e, e', zpow_one]
  · rw [← Finset.prod_inv_distrib]
    refine Fintype.prod_equiv (Fin.revPerm (n := D.q)) _ _ fun j => ?_
    have h : ¬ ((Fin.natAdd D.p j : Fin (D.p + D.q)) : ℕ) < D.p := by simp
    have e : HodgeCpt.rootIdx D (τ, Fin.natAdd D.p j) = ⟨.inr τ, Fin.rev j⟩ := by
      refine (dif_neg h).trans ?_
      congr 1
      apply Fin.ext
      have hj : (j : ℕ) < D.q := j.2
      show D.p + D.q - 1 - (D.p + (j : ℕ)) = D.q - ((j : ℕ) + 1)
      omega
    have e' : HodgeCpt.rootSgn D (τ, Fin.natAdd D.p j) = -1 := if_neg h
    rw [e, e', zpow_neg_one]
    rfl

end PositivityTheory.Xgn.ComponentDegreeAlt

open PositivityTheory.Xgn.ComponentDegreeAlt in
theorem PositivityTheory.Xgn.hodge_component_flag_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (τ : CMType H), Fl.RootLines xdeg e → (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ)) (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))).IsDegOn Set.univ y (∑ i, xdeg (τ, i)) (∏ i, e (τ, i)) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 Fl xdeg e τ hR
  have hli : ∀ s, LinearIndependent Ω (Fl.b s) := by
    obtain ⟨_, _, -, -, -, h, -⟩ := Fl.generic
    exact h
  refine ⟨Finset.prod_ne_zero_iff.2 fun i _ => (hR (τ, i)).1, fun p _ cc hcc => ?_⟩
  choose t ht hw using fun s => exists_gen_wedge (hli s) (Fl.sub s) p
  have hy : ∀ k, y ⟨k, cc k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hcc.1 k (Finset.mem_univ k)
  rw [lineLat_eq (wedge_ne_zero (hli _)) (wedge_ne_zero (hli _))
    (Finset.prod_ne_zero_iff.2 fun i _ => (ht _ i).1) (Finset.prod_ne_zero_iff.2 fun i _ => (ht _ i).1)
    (hw (.inl τ)) (hw (.inr τ)), ← prod_root D t τ]
  have hu : ∀ i : Fin (D.p + D.q), ∃ u : Ω, unitAt 𝔐.ξ p u ∧
      t (HodgeCpt.rootIdx D (τ, i)).1 (HodgeCpt.rootIdx D (τ, i)).2 ^ HodgeCpt.rootSgn D (τ, i) =
        u • (∏ k, y ⟨k, cc k⟩ ^ xdeg (τ, i) k) • e (τ, i) := fun i =>
    ZUnit.exists_of_span_eq (zpow_ne_zero _ (ht _ _).1)
      ((tens_unit_eq (ht _ _) _).symm.trans ((hR (τ, i)).2 p trivial cc hcc))
  choose u hu eu using hu
  have key : ∏ i : Fin (D.p + D.q), t (HodgeCpt.rootIdx D (τ, i)).1 (HodgeCpt.rootIdx D (τ, i)).2 ^
      HodgeCpt.rootSgn D (τ, i) =
      (∏ i, u i) * ((∏ k, y ⟨k, cc k⟩ ^ (∑ i, xdeg (τ, i)) k) • ∏ i, e (τ, i)) := by
    simp only [eu, smul_eq_mul, Finset.prod_mul_distrib, Finset.sum_apply, zpow_finsum (hy _)]
    rw [Finset.prod_comm]
  rw [key]
  exact span_unit_mul (unit_prod _ u hu) _
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XCoherentGens
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_coherent_gens

theorem mem_spanOver {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E]
    [Module Ω E] (R : Subalgebra o Ω) {S : Set E} {e : E} (he : e ∈ S) : e ∈ spanOver R S :=
  AddSubgroup.subset_closure ⟨1, one_mem R, e, he, (one_smul Ω e).symm⟩

theorem spanOver_le {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E]
    [Module Ω E] (R : Subalgebra o Ω) {S : Set E} {L : AddSubgroup E}
    (hL : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) (hS : ∀ e ∈ S, e ∈ L) : spanOver R S ≤ L := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨a, ha, e, he, rfl⟩
  exact hL a ha e (hS e he)

theorem spanOver_mono {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E]
    [Module Ω E] (R : Subalgebra o Ω) {S T : Set E} (h : S ⊆ T) : spanOver R S ≤ spanOver R T := by
  refine AddSubgroup.closure_mono ?_
  rintro _ ⟨a, ha, e, he, rfl⟩
  exact ⟨a, ha, e, h he, rfl⟩

theorem transition {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {K : Type} [Fintype K]
    [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) {c t : ∀ k, ι k}
    (ht : mseg x t ≠ 0) (a : K → ℤ) (m : ℕ) (hm : ∀ k, (m : ℤ) ≤ a k) :
    ∃ r ∈ chartRing o (mseg x) t,
      (chartMon x t a)⁻¹ * chartMon x c a = r * (mseg x c / mseg x t) ^ m := by
  refine ⟨∏ k, (x ⟨k, c k⟩ / x ⟨k, t k⟩) ^ (a k - m).toNat,
    prod_mem fun k _ => pow_mem (TwistedDualGensExist.ratio_mem (O := o) x ht k (c k)) _, ?_⟩
  simp only [chartMon, mseg]
  rw [← Finset.prod_div_distrib, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h : a k = (((a k - m).toNat + m : ℕ) : ℤ) := by
    have := hm k
    push_cast
    omega
  rw [← pow_add, ← zpow_natCast, ← h, div_zpow, div_eq_inv_mul]

end PositivityTheory.Xgn.A_coherent_gens

theorem PositivityTheory.Xgn.t_coherent_gens : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (V : Type) [AddCommGroup V] [Module Ω V] (Γ : (∀ k, ι k) → AddSubgroup V), IsLatFamily O x Γ → (∀ c, mseg x c ≠ 0 → ∃ S : Finset V, Γ c = spanOver (chartRing O (mseg x) c) (S : Set V)) → ∃ a₁ : K → ℤ, ∀ a : K → ℤ, a₁ ≤ a → ∃ (M : ℕ) (v : Fin M → V), ∀ c, mseg x c ≠ 0 → Γ c = spanOver (chartRing O (mseg x) c) (Set.range fun j => (chartMon x c a)⁻¹ • v j) := by
  classical
  intro O _ _ _ Ω _ _ K _ _ ι _ x V _ _ Γ ⟨hst, hov⟩ hfg
  choose! S hS using hfg
  let I := Σ c : {c : ∀ k, ι k // mseg x c ≠ 0}, S c.1
  have hmem : ∀ i : I, (i.2 : V) ∈ Γ i.1.1 := fun i => by
    rw [hS _ i.1.2]
    exact A_coherent_gens.mem_spanOver _ i.2.2
  have hex : ∀ p : I × {c : ∀ k, ι k // mseg x c ≠ 0}, ∃ m : ℕ,
      (mseg x p.1.1.1 / mseg x p.2.1) ^ m • (p.1.2 : V) ∈ Γ p.2.1 :=
    fun p => hov _ _ p.1.1.2 p.2.2 _ (hmem p.1)
  choose m hm using hex
  refine ⟨fun _ => ((∑ p, m p : ℕ) : ℤ), fun a ha => ?_⟩
  let e := Fintype.equivFin I
  refine ⟨_, fun j => chartMon x (e.symm j).1.1 a • ((e.symm j).2 : V), fun t ht => ?_⟩
  apply le_antisymm
  · rw [hS t ht]
    refine A_coherent_gens.spanOver_mono _ fun w hw => ⟨e ⟨⟨t, ht⟩, ⟨w, hw⟩⟩, ?_⟩
    have hne : chartMon x t a ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ =>
      zpow_ne_zero _ ((Finset.prod_ne_zero_iff.1 ht) k (Finset.mem_univ _))
    dsimp only
    rw [e.symm_apply_apply, smul_smul, inv_mul_cancel₀ hne, one_smul]
  · refine A_coherent_gens.spanOver_le _ (hst t ht) ?_
    rintro _ ⟨j, rfl⟩
    obtain ⟨r, hr, heq⟩ := A_coherent_gens.transition (o := O) x (c := (e.symm j).1.1) ht a
      (m (e.symm j, ⟨t, ht⟩)) fun k => le_trans (by
        exact Nat.cast_le.2
          (Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))) (ha k)
    dsimp only
    rw [smul_smul, heq, mul_smul]
    exact hst t ht r hr _ (hm (e.symm j, ⟨t, ht⟩))
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFormsExist
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_forms_exist

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] [DecidableEq K]
  {ι : K → Type}

theorem shift (x : (Σ k, ι k) → Ω) (t : ∀ k, ι k) (e : K → ℕ) {F : MRing ι O} {d : K → ℕ}
    (hF : IsMultiHomog F d) :
    ∃ G : MRing ι O, IsMultiHomog G (d + e) ∧ aeval x G = aeval x F * ∏ k, x ⟨k, t k⟩ ^ e k := by
  have h := IsWeightedHomogeneous.prod (Finset.univ : Finset K)
    (fun k => (X ⟨k, t k⟩ : MRing ι O) ^ e k) (fun k => e k • blockWeight ι ⟨k, t k⟩)
    (w := blockWeight ι)
    (fun k _ => (isWeightedHomogeneous_X O (blockWeight ι) ⟨k, t k⟩).pow (e k))
  have he : ∑ k, e k • blockWeight ι ⟨k, t k⟩ = e := by
    ext k'
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [he] at h
  refine ⟨F * ∏ k, (X ⟨k, t k⟩ : MRing ι O) ^ e k, IsWeightedHomogeneous.mul hF h, ?_⟩
  simp [map_prod]

def fracs (O : Type) [CommRing O] [Algebra O Ω] (x : (Σ k, ι k) → Ω) (s : ∀ k, ι k) : Subalgebra O Ω where
  carrier := {v | ∃ (d : K → ℕ) (F : MRing ι O), IsMultiHomog F d ∧ aeval x F = v * ∏ k, x ⟨k, s k⟩ ^ d k}
  mul_mem' := by
    rintro v w ⟨d, F, hF, eF⟩ ⟨e, G, hG, eG⟩
    refine ⟨d + e, F * G, IsWeightedHomogeneous.mul hF hG, ?_⟩
    simp only [map_mul, eF, eG, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring
  add_mem' := by
    rintro v w ⟨d, F, hF, eF⟩ ⟨e, G, hG, eG⟩
    obtain ⟨F', hF', eF'⟩ := shift x s e hF
    obtain ⟨G', hG', eG'⟩ := shift x s d hG
    rw [add_comm e d] at hG'
    refine ⟨d + e, F' + G', IsWeightedHomogeneous.add hF' hG', ?_⟩
    simp only [map_add, eF', eG', eF, eG, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring
  algebraMap_mem' r := ⟨0, C r, isWeightedHomogeneous_C _ _, by simp⟩

theorem chartRing_le_fracs (x : (Σ k, ι k) → Ω) (s : ∀ k, ι k) (hs : mseg x s ≠ 0) :
    chartRing O (mseg x) s ≤ fracs O x s := by
  unfold chartRing
  rw [Algebra.adjoin_le_iff]
  rintro _ ⟨j, rfl⟩
  refine ⟨fun _ => 1, ∏ k, (X ⟨k, j k⟩ : MRing ι O), ?_, ?_⟩
  · have h := IsWeightedHomogeneous.prod (Finset.univ : Finset K)
      (fun k => (X ⟨k, j k⟩ : MRing ι O)) (fun k => blockWeight ι ⟨k, j k⟩)
      (w := blockWeight ι) (fun k _ => isWeightedHomogeneous_X O (blockWeight ι) ⟨k, j k⟩)
    have he : ∑ k, blockWeight ι ⟨k, j k⟩ = fun _ => 1 := by
      ext k'
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [he] at h
    exact h
  · simp only [map_prod, aeval_X, pow_one]
    have hm : ∏ k, x ⟨k, s k⟩ = mseg x s := rfl
    rw [hm, div_mul_cancel₀ _ hs]
    try rfl

end PositivityTheory.Xgn.A_forms_exist
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSJoinvertdiv
section
theorem PositivityTheory.Xgn.t_s_joinvertdiv : GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisor.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisor.proof
end

