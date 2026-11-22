import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MGrCard
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.grCard_of :
    GrCard := by
  intro k H _ _ _ _ n j hn
  have hdim : Module.finrank k H = Module.finrank k (Fin n → k) := by simp [hn]
  let e : H ≃ₗ[k] (Fin n → k) := LinearEquiv.ofFinrankEq H (Fin n → k) hdim
  apply Nat.card_congr
  refine (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv ?_
  intro D
  change Module.finrank k D = j ↔ Module.finrank k (D.map (e : H →ₗ[k] (Fin n → k))) = j
  rw [LinearEquiv.finrank_map_eq]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MKillLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

namespace UpperTheory.Gal.crystallineComparison.Mod

private theorem away_local {B : Type} [CommRing B] (f : B) (p : PrimeSpectrum B)
    (hp : p ∈ PrimeSpectrum.basicOpen f) (hs : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) ⊆ {p}) :
    IsLocalRing (Localization.Away f) := by
  have hrange := PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  have hinj := PrimeSpectrum.localization_comap_injective (Localization.Away f) (Submonoid.powers f)
  have key : ∀ q : PrimeSpectrum (Localization.Away f),
      PrimeSpectrum.comap (algebraMap B (Localization.Away f)) q = p := by
    intro q
    have hq : PrimeSpectrum.comap (algebraMap B (Localization.Away f)) q ∈
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) := by
      rw [← hrange]
      exact ⟨q, rfl⟩
    exact hs hq
  obtain ⟨q, -⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away f))) := by
    rw [hrange]
    exact hp
  obtain ⟨M, hM, -⟩ := Ideal.exists_le_maximal q.asIdeal q.2.ne_top
  refine IsLocalRing.of_unique_max_ideal ⟨M, hM, fun N hN => ?_⟩
  have h := hinj ((key ⟨N, hN.isPrime⟩).trans (key ⟨M, hM.isPrime⟩).symm)
  exact congrArg PrimeSpectrum.asIdeal h

private theorem exists_eps (κ B : Type) [Field κ] [IsAlgClosed κ] [CommRing B] [Algebra κ B] [Module.Finite κ B]
    (f : B) (m : Ideal B) [hm : m.IsMaximal] (hf : f ∉ m) :
    Nonempty (Localization.Away f →ₐ[κ] κ) := by
  haveI : Module.Finite κ (B ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ κ m).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Algebra.IsAlgebraic κ (B ⧸ m) := Algebra.IsAlgebraic.of_finite κ (B ⧸ m)
  let φ : B ⧸ m →ₐ[κ] κ := IsAlgClosed.lift
  let ψ : B →ₐ[κ] κ := φ.comp (Ideal.Quotient.mkₐ κ m)
  refine ⟨IsLocalization.liftAlgHom (M := Submonoid.powers f) (f := ψ) ?_⟩
  rintro ⟨y, n, rfl⟩
  simp only [map_pow]
  refine IsUnit.pow _ (isUnit_iff_ne_zero.mpr ?_)
  intro h
  apply hf
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply φ.toRingHom.injective
  rw [map_zero]
  exact h

private theorem local_kill (κ : Type) [Field κ] (A A' : Over (Sp κ)) [GrpObj A] [GrpObj A'] (χ : A ⟶ A') [IsMonHom χ]
    (P : ∀ T : Over (Sp κ), (T ⟶ A) → Prop) (hsub : IsSub A P)
    (h1 : ∀ g : 𝟙_ (Over (Sp κ)) ⟶ A, P _ g → g ≫ χ = 1)
    (Λ : Type) [CommRing Λ] [Algebra κ Λ] (ε : Λ →ₐ[κ] κ)
    (h2 : ∀ g : algPt κ Λ ⟶ A, P _ g → Inf ε g → g ≫ χ = 1)
    (g : algPt κ Λ ⟶ A) (hP : ∀ (T : Over (Sp κ)) (y : T ⟶ algPt κ Λ), P T (y ≫ g)) : g ≫ χ = 1 := by
  let s : 𝟙_ (Over (Sp κ)) ⟶ algPt κ Λ := Over.homMk (spMap ε.toRingHom) (by
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 1
    ext x
    simp)
  let π : algPt κ Λ ⟶ 𝟙_ (Over (Sp κ)) := toUnit _
  have hsπ : s ≫ π = 𝟙 _ := toUnit_unique _ _
  let g0 : algPt κ Λ ⟶ A := π ≫ s ≫ g
  have hg : P _ g := by simpa using hP _ (𝟙 _)
  have hg0 : P _ g0 := by simpa [g0] using hP _ (π ≫ s)
  have hsg : P _ (s ≫ g) := hP _ s
  have hh : P _ (g * g0⁻¹) := ((hsub _).2 _ _ hg hg0)
  have hs1 : s ≫ (g * g0⁻¹) = 1 := by
    rw [MonObj.comp_mul, GrpObj.comp_inv]
    simp only [g0, ← Category.assoc, hsπ, Category.id_comp, mul_inv_cancel]
  have hinf : Inf ε (g * g0⁻¹) := by
    have := congrArg Over.Hom.left hs1
    simpa [Inf, s] using this
  have e1 : (g * g0⁻¹) ≫ χ = 1 := h2 _ hh hinf
  have e2 : g0 ≫ χ = 1 := by
    simp only [g0, Category.assoc, h1 _ hsg, MonObj.comp_one]
  have : g = (g * g0⁻¹) * g0 := by rw [inv_mul_cancel_right]
  rw [this, MonObj.mul_comp, e1, e2]
  exact _root_.mul_one _

theorem killLocal_of : KillLocal := by
  intro κ _ _ A A' _ _ χ hχ P d hrep hsub h1 h2 T g hg
  obtain ⟨B, _, _, hfin, hfree, -, i, hmono, hi⟩ := hrep
  obtain ⟨y, rfl⟩ := (hi T g).2 hg
  suffices hmain : i ≫ χ = 1 by rw [Category.assoc, hmain, comp_one]
  haveI : IsArtinianRing B := IsArtinianRing.of_finite κ B
  have hpt : ∀ p : PrimeSpectrum B, ∃ f : B, p ∈ PrimeSpectrum.basicOpen f ∧
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) ⊆ {p} := by
    intro p
    obtain ⟨_, ⟨f, rfl⟩, hp, hs⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (Set.mem_singleton p) (isOpen_discrete _)
    exact ⟨f, hp, hs⟩
  choose s hs hs' using hpt
  have hspan : Ideal.span (Set.range s) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hs ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of B) s hspan).openCover _ _ fun p => ?_
  change spMap (algebraMap B (Localization.Away (s p))) ≫ _ = spMap (algebraMap B (Localization.Away (s p))) ≫ _
  haveI := away_local (s p) p (hs p) (hs' p)
  haveI hmax : p.asIdeal.IsMaximal := p.2.isMaximal'
  obtain ⟨ε⟩ := exists_eps κ B (s p) p.asIdeal (hs p)
  let j : algPt κ (Localization.Away (s p)) ⟶ algPt κ B := Over.homMk (spMap (algebraMap B (Localization.Away (s p)))) (by
    change spMap (algebraMap B (Localization.Away (s p))) ≫ spMap (algebraMap κ B) = spMap (algebraMap κ (Localization.Away (s p)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])
  have hk : (j ≫ i) ≫ χ = 1 := local_kill κ A A' χ P hsub h1 _ ε (fun g hg hI => h2 _ ε g hg hI) (j ≫ i)
    (fun T y => (hi T _).1 ⟨y ≫ j, by simp⟩)
  have hk' : j ≫ i ≫ χ = j ≫ 1 := by rw [comp_one, ← Category.assoc, hk]
  exact congrArg (fun t => t.left) hk'

end UpperTheory.Gal.crystallineComparison.Mod
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MLiftFF
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.liftFF_of :
    AlgOf → LiftPt → LiftFF := by
  intro hAlg hPt S K h hfin hflat V _ _ _ _ z g hg
  obtain ⟨B, _, _, k, hfinB, hfreeB, hp⟩ := hAlg S K h hfin hflat V z
  haveI : Module.Finite V B := hfinB
  haveI : Module.Free V B := hfreeB
  let u : Sp (IsLocalRing.ResidueField V) ⟶ Sp B := hp.lift g (resPt V) hg
  have huk : u ≫ k = g := hp.lift_fst _ _ _
  have hua : u ≫ spMap (algebraMap V B) = resPt V := hp.lift_snd _ _ _
  let χ : B →+* IsLocalRing.ResidueField V := (Spec.preimage u).hom
  have hχ : spMap χ = u := by
    show Spec.map (CommRingCat.ofHom (Spec.preimage u).hom) = u
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hχa : χ.comp (algebraMap V B) = IsLocalRing.residue V := by
    have h1 : Spec.map (CommRingCat.ofHom (χ.comp (algebraMap V B))) =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
      exact (congrArg (· ≫ spMap (algebraMap V B)) hχ).trans hua
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  obtain ⟨z₀, hz₀⟩ := hPt V B χ hχa
  refine ⟨spMap z₀.toRingHom ≫ k, ?_, ?_⟩
  · have hc : z₀.toRingHom.comp (algebraMap V B) = RingHom.id V := by
      ext x
      exact z₀.commutes x
    have h3 : spMap z₀.toRingHom ≫ spMap (algebraMap V B) = 𝟙 _ := by
      show Spec.map (CommRingCat.ofHom z₀.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap V B)) = 𝟙 _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
      exact Spec.map_id _
    rw [Category.assoc, hp.w, ← Category.assoc, h3, Category.id_comp]
  · have h4 : resPt V ≫ spMap z₀.toRingHom = u := by
      rw [← hχ, ← hz₀]
      show Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) ≫ Spec.map (CommRingCat.ofHom z₀.toRingHom) =
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue V).comp z₀.toRingHom))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← Category.assoc, h4, huk]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MLiftPt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.liftPt_of :
    LiftPt := by
  intro V _ _ _ _ B _ _ _ _ χ hχ
  classical
  let m : Ideal B := RingHom.ker χ
  haveI : m.IsPrime := RingHom.ker_isPrime χ
  obtain ⟨q, hqmin, hqm⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := m) bot_le
  haveI : q.IsPrime := hqmin.1.1
  have hnzd : ∀ v : V, v ≠ 0 → algebraMap V B v ∈ nonZeroDivisors B := by
    intro v hv
    rw [mem_nonZeroDivisors_iff]
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [← Algebra.smul_def] at hx
      exact (smul_eq_zero.mp hx).resolve_left hv
    · rw [← Algebra.commutes, ← Algebra.smul_def] at hx
      exact (smul_eq_zero.mp hx).resolve_left hv
  have hinj : Function.Injective (algebraMap V (B ⧸ q)) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hv0
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem] at hv
    exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hqmin) hv (hnzd v hv0)
  have hK : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective V (FractionRing V)
  haveI : Module.IsTorsionFree V (B ⧸ q) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r x h => ?_
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left fun h => hinj (by rw [h, map_zero])
  haveI : Module.IsTorsionFree V (FractionRing V) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r x h => ?_
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left fun h => hK (by rw [h, map_zero])
  haveI : Algebra.IsIntegral V (B ⧸ q) := inferInstance
  haveI : Algebra.IsAlgebraic V (B ⧸ q) := Algebra.IsIntegral.isAlgebraic
  let φ : (B ⧸ q) →ₐ[V] FractionRing V := IsAlgClosed.lift
  have hker : RingHom.ker (φ : (B ⧸ q) →+* FractionRing V) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := V)
    ext v
    simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot, RingHom.coe_coe, AlgHom.commutes]
    exact map_eq_zero_iff _ hK
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ RingHom.ker (φ : (B ⧸ q) →+* FractionRing V) := hx
    rwa [hker] at this
  let ψ : B →ₐ[V] FractionRing V := φ.comp (Ideal.Quotient.mkₐ V q)
  have hψ : ∀ b, ψ b ∈ (⊥ : Subalgebra V (FractionRing V)) := by
    intro b
    rw [Algebra.mem_bot]
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      ((Algebra.IsIntegral.isIntegral (R := V) (Ideal.Quotient.mkₐ V q b)).map φ)
    exact ⟨y, hy⟩
  let e := Algebra.botEquivOfInjective hK
  let z : B →ₐ[V] V := e.toAlgHom.comp (ψ.codRestrict ⊥ hψ)
  have hz : ∀ b, algebraMap V (FractionRing V) (z b) = ψ b := by
    intro b
    have h1 := e.symm_apply_apply (ψ.codRestrict ⊥ hψ b)
    have h2 := e.symm.commutes (z b)
    have h3 : (algebraMap V V) (z b) = e (ψ.codRestrict ⊥ hψ b) := rfl
    rw [h3, h1] at h2
    have h4 := congrArg (fun s : (⊥ : Subalgebra V (FractionRing V)) => (s : FractionRing V)) h2
    simpa using h4.symm
  refine ⟨z, ?_⟩
  ext b
  have hc : b - algebraMap V B (z b) ∈ q := by
    have h0 : z (b - algebraMap V B (z b)) = 0 := by
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have h1 : ψ (b - algebraMap V B (z b)) = 0 := by
      rw [← hz, h0, map_zero]
    have h2 : Ideal.Quotient.mkₐ V q (b - algebraMap V B (z b)) = 0 :=
      hφinj (by rw [map_zero]; exact h1)
    rwa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at h2
  have hm : χ (b - algebraMap V B (z b)) = 0 := hqm hc
  rw [map_sub, sub_eq_zero] at hm
  rw [hm, ← RingHom.comp_apply, hχ]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MOrdReadOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem exA (hIn : CountIn) (hOut : CountOut) {n : ℕ} {P : Type} {I : Fin (n + 1) → Type}
    (v : ∀ j, I j → P) {k H : Type} [Field k] [Finite k] [AddCommGroup H] [Module k H]
    [Module.Finite k H] (C : Submodule k H) (e : ∀ j, I j ≃ Gr k H j)
    (hn : Module.finrank k H = n) (hC : Module.finrank k C = 1) :
    ∃ (A : Submodule k (H ⧸ C) → P) (D : Submodule k (H ⧸ C) → Submodule k H),
      (∀ E, ¬ C ≤ D E) ∧ (∀ E, (D E).map C.mkQ = E) ∧
      (∀ E, Module.finrank k (D E) = Module.finrank k E) ∧
      (∀ E : Submodule k (H ⧸ C), Module.finrank k E < n + 1) ∧
      ∀ E (j' : Fin (n + 1)) (hj' : Module.finrank k (D E) = j'),
        A E = v j' ((e j').symm ⟨D E, hj'⟩) := by
  classical
  have hex : ∀ E : Submodule k (H ⧸ C), ∃ D : Submodule k H, ¬ C ≤ D ∧ D.map C.mkQ = E := by
    intro E
    have hcard := hOut k H C hC E
    have hpos : 0 < Nat.card {D : Submodule k H // ¬ C ≤ D ∧ D.map C.mkQ = E} := by
      rw [hcard]
      exact pow_pos Nat.card_pos _
    obtain ⟨⟨D, hD⟩⟩ := (Nat.card_pos_iff.mp hpos).1
    exact ⟨D, hD⟩
  choose D hDC hDE using hex
  have hrk : ∀ E, Module.finrank k (D E) = Module.finrank k E := by
    intro E
    rw [(hIn k H C hC).2.2 (D E) (hDC E), hDE E]
  have hlt : ∀ E : Submodule k (H ⧸ C), Module.finrank k E < n + 1 := by
    intro E
    have h1 : Module.finrank k E ≤ Module.finrank k (H ⧸ C) := Submodule.finrank_le E
    have h2 : Module.finrank k (H ⧸ C) ≤ Module.finrank k H := Submodule.finrank_quotient_le C
    omega
  refine ⟨fun E => v ⟨Module.finrank k (D E), by rw [hrk]; exact hlt E⟩
      ((e _).symm ⟨D E, rfl⟩), D, hDC, hDE, hrk, hlt, ?_⟩
  intro E j' hj'
  obtain rfl : j' = ⟨Module.finrank k (D E), by rw [hrk]; exact hlt E⟩ := Fin.ext hj'.symm
  rfl

theorem UpperTheory.Gal.crystallineComparison.Mod.ordReadOf_of :
    CountIn → CountOut → OrdReadOf := by
  intro hIn hOut q n P F I v k H _ _ _ _ _ C e hq hn hC h1 h2
  obtain ⟨A, D, hDC, hDE, hrk, hlt, hA⟩ := exA hIn hOut v C e hn hC
  refine ⟨k, H, _, inferInstance, _, _, inferInstance, C, A, e, hq, hn, hC, fun j i => ⟨fun hle => ?_, fun hnle => ?_⟩⟩
  · set E := ((e j i).1).map C.mkQ with hEdef
    have hj : (j : ℕ) = Module.finrank k E + 1 := by
      rw [← (e j i).2, (hIn k H C hC).2.1 _ hle]
    let j' : Fin (n + 1) := ⟨Module.finrank k E, hlt E⟩
    have hj' : Module.finrank k (D E) = j' := hrk E
    have hs : ((e j') ((e j').symm ⟨D E, hj'⟩)).1 = D E :=
      congrArg Subtype.val (Equiv.apply_symm_apply (e j') ⟨D E, hj'⟩)
    rw [hA E j' hj']
    apply h2 j j' i
    · exact hj
    · exact hle
    · rw [hs]; exact hDC E
    · rw [hs, hDE E]
  · set E := ((e j i).1).map C.mkQ with hEdef
    have hj : Module.finrank k (D E) = j := by
      rw [hrk E, ← (e j i).2, (hIn k H C hC).2.2 _ hnle]
    have hs : ((e j) ((e j).symm ⟨D E, hj⟩)).1 = D E :=
      congrArg Subtype.val (Equiv.apply_symm_apply (e j) ⟨D E, hj⟩)
    rw [hA E j hj]
    apply h1 j i
    · exact hnle
    · rw [hs]; exact hDC E
    · rw [hs, hDE E]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPicFrob
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace UpperTheory.Gal.crystallineComparison.Mod

private theorem gm_absFrob (p f : ℕ) (hp : p.Prime) (X : Scheme.{0}) (h : (p : Γ(X, ⊤)) = 0) (y : X)
    (U : X.Opens) (hy : y ∈ U) (a : Γ(X, U)ˣ) :
    gm (GlobalTheory.SS.FrobField.absFrob X p f hp h) y U a = gm (𝟙 X) y U a ^ p ^ f := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, gm_val _ _ _ hy, gm_val _ _ _ hy, ← map_pow]
  rfl

theorem picFrob_of : PicFrob := by
  unfold PicFrob
  intro p f hp X h c
  obtain ⟨L, hL, rfl⟩ := GlobalTheory.CechPic.cls_surj c
  set F := GlobalTheory.SS.FrobField.absFrob X p f hp h
  have hB : (lbPow L (p ^ f)).IsLB := by
    rw [lbPow]
    exact LB.isLB_linComb hL _ _
  have hmem : ∀ (J : PUnit.{1} → L.ι) (x : X), x ∈ L.U (J PUnit.unit) →
      x ∈ L.wchart (fun _ => 𝟙 X) J := by
    intro J x hx
    show x ∈ ⋂ k, (𝟙 X : X ⟶ X) ⁻¹' (L.U (J k) : Set X)
    rw [Set.mem_iInter]
    intro k
    exact hx
  rw [← GlobalTheory.CechPic.cls_pull hL F (pull_isLB hL F), ← GlobalTheory.CechPic.cls_lbPow hL (p ^ f) hB,
    GlobalTheory.CechPic.cls_eq_iff]
  refine GlobalTheory.CechPic.iso_of_chart hB ⟨fun J => J, ?_, ?_⟩
  · intro J x hx
    exact hmem J x (mem_pull.1 hx)
  · intro y i j hi hj
    have hi' : y ∈ L.U (i PUnit.unit) := mem_pull.1 hi
    have hj' : y ∈ L.U (j PUnit.unit) := mem_pull.1 hj
    rw [gm_pull_g L F (𝟙 X) y i j hi hj]
    erw [gm_linComb L (fun _ => 𝟙 X) (fun _ => ((p ^ f : ℕ) : ℤ)) (𝟙 X) y i j (hmem i y hi')
      (hmem j y hj')]
    rw [Category.id_comp, Category.comp_id, Fintype.prod_unique, zpow_natCast]
    exact gm_absFrob p f hp X h y (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ⟨hi', hj'⟩ _

end UpperTheory.Gal.crystallineComparison.Mod
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MRedPts
section
namespace UpperTheory.Gal.crystallineComparison.Mod

theorem redPts_of : RedPts := by
  intro k H X _ _ _ _ _ C ρ h D
  obtain ⟨s, hs⟩ : ∃ s : H ⧸ C → H, Function.RightInverse s C.mkQ :=
    ⟨Function.surjInv (Submodule.mkQ_surjective C), Function.rightInverse_surjInv _⟩
  let g : H ⧸ C → X := fun q => ρ (s q)
  have hg : ∀ a, ρ a = g (C.mkQ a) := by
    intro a
    refine (h _ _).2 ?_
    have h1 : C.mkQ (s (C.mkQ a)) = C.mkQ a := hs _
    have h2 := (Submodule.Quotient.eq C).1 h1
    have h3 : a - s (C.mkQ a) = -(s (C.mkQ a) - a) := by abel
    rw [h3]
    exact C.neg_mem h2
  have hinj : Function.Injective g := by
    intro q1 q2 hq
    have hm := (h _ _).1 hq
    have e := (Submodule.Quotient.eq C).2 hm
    simpa [Submodule.mkQ_apply, hs q1, hs q2] using
      (show C.mkQ (s q1) = C.mkQ (s q2) from e)
  have himg : ∀ E : Submodule k H, ρ '' (E : Set H) = g '' ((Submodule.map C.mkQ E : Submodule k (H ⧸ C)) : Set (H ⧸ C)) := by
    intro E
    rw [Submodule.map_coe, Set.image_image]
    exact Set.image_congr (fun a _ => hg a)
  have hcard : ∀ V : Submodule k (H ⧸ C), Nat.card V = Nat.card k ^ Module.finrank k V := by
    intro V
    have : Finite (H ⧸ C) := Module.finite_of_finite k
    letI := Fintype.ofFinite k
    letI := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  refine ⟨?_, ?_⟩
  · rw [himg D, Nat.card_image_of_injective hinj]
    exact hcard _
  · intro D' hD
    rw [himg D, himg D', hD]

end UpperTheory.Gal.crystallineComparison.Mod
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MRepOfFF
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.repOfFF_of :
    AlgOf → RepOfFF := by
  rintro hA κ _ A P ⟨K, i, hm, hfin, hfl, hP⟩
  obtain ⟨B, _, _, k, hf, hfr, pb⟩ := hA (Sp κ) K.left K.hom hfin hfl κ (𝟙 _)
  have hk : IsIso k := pb.isIso_fst_of_isIso
  have hw : k ≫ K.hom = spMap (algebraMap κ B) := by
    simpa using pb.w
  let e : algPt κ B ≅ K := Over.isoMk (asIso k) hw
  refine ⟨Module.finrank κ B, B, ‹_›, ‹_›, hf, hfr, rfl, e.hom ≫ i, inferInstance, fun T g => ?_⟩
  rw [← hP T g]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y ≫ e.hom, by simpa using hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y ≫ e.inv, by simpa using hy⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MResClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.resClosed_of :
    ResClosed := by
  intro V _ _ _ _
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hm hirr
  have hsurj : Function.Surjective (IsLocalRing.residue V) := IsLocalRing.residue_surjective
  have hl : p ∈ Polynomial.lifts (IsLocalRing.residue V) :=
    Polynomial.mem_lifts _ |>.2 (Polynomial.map_surjective _ hsurj p)
  obtain ⟨P, hP, hdeg, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
  have hinj : Function.Injective (algebraMap V (FractionRing V)) :=
    IsFractionRing.injective V (FractionRing V)
  have hpos : 0 < P.natDegree := hdeg ▸ hirr.natDegree_pos
  have hd : (P.map (algebraMap V (FractionRing V))).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective hinj]
    exact (Polynomial.natDegree_pos_iff_degree_pos.1 hpos).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd
  have hint : IsIntegral V x := by
    refine ⟨P, hPm, ?_⟩
    simpa [Polynomial.IsRoot.def, Polynomial.eval_map] using hx
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hy : P.eval y = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact hx
  refine ⟨IsLocalRing.residue V y, ?_⟩
  rw [← hP, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]
end

