import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SocleOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Outright
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Bundle0003
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0752
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0711
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0048
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0066
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0594
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0604
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0798
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0608
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0804
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0600
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0609
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0706
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0806
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0801
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0113
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0788
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0620
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0084
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1972
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0311
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0807
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0800
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0789

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSocleProdIrrCongr
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.LocGL

theorem isSocle_prodIrr_congr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} {y z : Fin h → IrrGL k} (e : y = z)
    (hy : ∑ a, (y a).1 = N) (hz : ∑ a, (z a).1 = N) (H : IsSocle π (prodIrr y hy)) :
    IsSocle π (prodIrr z hz) := by
  subst e
  exact H

theorem socleOne : PositivityTheory.SphericalProduct.SocleOne := by
  intro k _ _ _ _ _ n ξ hξ hanti hd
  let x : Fin n → IrrGL k := fun i =>
    IrrGL.ofChar (ξ (Fin.rev i)) (isSmoothChar_of_isUnram (hξ (Fin.rev i)))
  have hLF : LFactors (PositivityTheory.SphericalProduct.msOne ξ hξ) x :=
    ⟨_, GlobalTheory.CompanionTheory.OneTermOrder.isOrderedForm_single_rev k n ξ hξ hanti, fun i => isLSeg_single k _ _⟩
  have hd1 : ∑ a, (x a).1 = n := by simp [x, IrrGL.ofChar]
  have hd2 : ∑ a, (x (Fin.rev a)).1 = n := by simp [x, IrrGL.ofChar]
  refine ⟨?_, ?_⟩
  · obtain ⟨π, hπ⟩ := PositivityTheory.Exh.standardCosocleGL_holds k _ n n x hd1 hLF
    have hL : IsL (PositivityTheory.SphericalProduct.msOne ξ hξ) π.ρ := ⟨n, x, hd1, hLF, hπ⟩
    exact ⟨IrrGL.of π.ρ π.smooth π.irr, rfl, hL.of_equiv (IrrGL.equivOf _ _ _)⟩
  · intro V _ _ π hL
    have hS := PositivityTheory.Exh.lSocleGL_of GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k _ n n x hd2 hLF π hL
    refine isSocle_prodIrr_congr ?_ _ hd hS
    funext a
    simp only [x, Function.comp, Fin.rev_rev]

end GlobalTheory.CompanionTheory.LocGL
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LOneSatakeBound
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.OneSat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_unifU : valuation k ((Zls.unifU k : kˣ) : k) = uniformizer k := by
  have hϖ := Zls.irreducible_unif (k := k)
  apply le_antisymm
  · exact le_uniformizer_iff.2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hϖ.not_isUnit)
  · obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k)
    have hlt : valuation k y < 1 := hy ▸ uniformizer_lt_one
    rw [← hy]
    exact (mem_cball_uniformiser hϖ (x := Zls.unifU k) rfl ⟨y, hlt.le⟩).2
      (Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 hlt)

theorem hasSatake_of_equiv {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin n) k) V} {σ : Representation ℂ (GL (Fin n) k) W} {α : Fin n → ℂˣ}
    (φ : π.Equiv σ) (h : HasSatake π α) : HasSatake σ α := by
  refine ⟨GlobalTheory.Parabolic.isIrreducible_of_equiv φ h.1, ?_, ?_⟩
  · obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 h.2.1
    refine (Submodule.ne_bot_iff _).2 ⟨φ v, fun g => ?_, fun e => h0 (φ.toLinearEquiv.injective ?_)⟩
    · have h1 := hv g
      have e : φ (π g v) = σ g (φ v) := φ.toIntertwiningMap.isIntertwining _ _ g v
      rw [← e, h1, map_smul]
    · simpa using e
  · exact (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans h.2.2

theorem isUnramChar_of_isCusp_of_isSpherical [CharZero k] (x : IrrGL k) (hx : x.IsCusp) (hs : IsSpherical x.rep) :
    x.IsUnramChar := by
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hadm : IsAdmissible x.rep := (hBZ k).1 (Fin x.1) x.2.rep.V x.rep x.2.rep.smooth x.2.rep.irr
  have hI : fixed x.rep (iwahori k (Fin x.1)) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    exact hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm x.2.rep.irr hI
  have hχ : ∀ i, IsSmoothChar (unrChar k (α i)) := fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))
  have h1 := GlobalTheory.T.supercuspidalSupport_of_principalSeries_subquotient k x.1 (fun i => unrChar k (α i)) hχ x.2.rep hα
  have h2 : HasSupport x.rep {x} := hasSupport_self hx
  have he := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma hBZ h1 h2
  have hmem : x ∈ (Finset.univ.val.map fun i => IrrGL.ofChar (unrChar k (α i)) (hχ i)) := by
    rw [he]; exact Multiset.mem_singleton_self x
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hmem
  exact ⟨unrChar k (α i), isUnram_unrChar k (α i), hi.symm⟩

theorem len_eq_one [CharZero k] (Δ : Segment k) (y : IrrGL k) (hL : IsLSeg Δ y.rep) (hS : IsSpherical y.rep) :
    Δ.len = 1 := by
  have hLM := PositivityTheory.Exh.langlandsMultisegments_holds
  have hSC := PositivityTheory.Exh.standardCosocleGL_holds
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  obtain ⟨N, c⟩ := y
  obtain ⟨hd, hc⟩ := id hL
  have hsub : IsSubquotient c.rep.ρ (prodIrr Δ.term hd) := hc.isSubquotient
  have hsph := GlobalTheory.T.isSpherical_factor_of_spherical_subquotient k Δ.len N Δ.term hd _ c.rep.ρ hsub hS
  have h0 : Δ.term ⟨0, Δ.len_pos⟩ = Δ.first := by simp [Segment.term]
  have key : ∀ x z : IrrGL k, x = z → IsSpherical x.rep → IsSpherical z.rep := by
    rintro _ _ rfl h; exact h
  have hU : Δ.first.IsUnramChar :=
    isUnramChar_of_isCusp_of_isSpherical Δ.first Δ.isCusp_first (key _ _ h0 (hsph _))
  obtain ⟨μ, hμ, hfirst⟩ := hU
  have hμs := isSmoothChar_of_isUnram hμ
  have hterm : ∀ a, Δ.term a = IrrGL.ofChar (μ * absPow k ((a : ℕ) : ℂ)) (hμs.mul (isSmoothChar_absPow _)) :=
    fun a => by simp only [Segment.term, IrrGL.nu, hfirst, IrrGL.tw_ofChar]
  have hd1 : Δ.d = 1 := congrArg Sigma.fst hfirst
  have hN : N = Δ.len := by
    have h2 : ∑ a, (Δ.term a).1 = N := hd
    rw [Segment.sum_term_fst, Segment.deg, hd1, mul_one] at h2
    exact h2.symm
  subst hN
  let Γ := Segment.ofChar μ hμs Δ.len Δ.len_pos
  have hterm' : ∀ a, Γ.term a = IrrGL.ofChar (μ * absPow k ((a : ℕ) : ℂ)) (hμs.mul (isSmoothChar_absPow _)) :=
    fun a => by
      show (IrrGL.ofChar μ hμs).nu _ = _
      simp only [IrrGL.nu, IrrGL.tw_ofChar]
  have hd' : ∑ a, (Γ.term a).1 = Δ.len := (Segment.sum_term_fst _).trans (mul_one _)
  have hP := GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries Δ.term hd _ _ hterm
  have hP' := GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries Γ.term hd' _ _ hterm'
  let χ' := μ * absPow k (((Δ.len : ℂ) - 1) / 2)
  have hu' : IsUnram χ' := fun x hx => by
    rw [MonoidHom.mul_apply, hμ x hx, isUnram_absPow k _ x hx, one_mul]
  have hχs : IsSmoothChar χ' := isSmoothChar_of_isUnram hu'
  obtain ⟨f, hf⟩ := embeds_detRep_segment hμs Δ.len_pos hd'
  have hϖ := valuation_unifU (k := k)
  have hu : ∀ i : Fin Δ.len, IsUnram (μ * absPow k ((i : ℕ) : ℂ)) := fun i x hx => by
    rw [MonoidHom.mul_apply, hμ x hx, isUnram_absPow k _ x hx, one_mul]
  let α : Fin Δ.len → ℂˣ := fun i => (μ * absPow k ((i : ℕ) : ℂ)) (Zls.unifU k)
  have heq : (fun i => unrChar k (α i)) = fun i : Fin Δ.len => μ * absPow k ((i : ℕ) : ℂ) :=
    funext fun i => (eq_unrChar (hu i) hϖ).symm
  have hA : HasSatake c.rep.ρ α := ⟨c.rep.irr, hS, by rw [heq]; exact hsub.trans hP⟩
  have hB : HasSatake (IrrRep.det (Fin Δ.len) χ' hχs).ρ α :=
    ⟨(IrrRep.det (Fin Δ.len) χ' hχs).irr, isSpherical_detRep hu',
      by rw [heq]; exact (IsSubquotient.of_injective f hf).trans hP'⟩
  obtain ⟨E⟩ := GlobalTheory.T.nonempty_equiv_of_same_satakeParameters hBZ k Δ.len α c.rep (IrrRep.det (Fin Δ.len) χ' hχs) hA hB
  have hL2 := (GlobalTheory.T.isLanglandsClassification_detCharacter hSC k Δ.len χ' hχs).of_equiv E.symm
  have hL1 := hL.isL
  have hm := (hLM k).1 _ _ ⟨Δ.len, c⟩ hL1 hL2
  have := congrArg Multiset.card hm
  simpa using this.symm

theorem isL_single_unrChar [CharZero k] (x : IrrGL k) (α : Fin x.1 → ℂˣ) (hsat : HasSatake x.rep α) :
    IsL (Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (unrChar k (α i))
      (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _)) x.rep := by
  obtain ⟨𝔪, hL⟩ := PositivityTheory.Exh.langlandsExhaustionGL_holds k x
  obtain ⟨h, y, hd, ⟨Δ, hord, hseg⟩, hcos⟩ := id hL
  have hsphy : ∀ a, IsSpherical (y a).rep :=
    GlobalTheory.T.isSpherical_factor_of_spherical_subquotient k h x.1 y hd x.2.rep.V x.rep hcos.isSubquotient hsat.2.1
  have hlen : ∀ i, (Δ i).len = 1 := fun i => len_eq_one (Δ i) (y i) (hseg i) (hsphy i)
  have hsingle : ∀ i, Δ i = Segment.single (Δ i).first (Δ i).isCusp_first := fun i =>
    Segment.ext_first rfl (by rw [hlen i]; rfl)
  have hms : ∀ i, (Δ i).ms = {(Δ i).first} := fun i =>
    (congrArg Segment.ms (hsingle i)).trans (Segment.ms_single _ _)
  have h1 : HasSupport x.rep (∑ a, (Δ a).ms) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (fun a => (hseg a).hasSupport) x.2.rep.irr
      hcos.isSubquotient
  have h2 := GlobalTheory.T.supercuspidalSupport_of_principalSeries_subquotient k x.1 (fun i => unrChar k (α i))
    (fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))) x.2.rep hsat.2.2
  have heq := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma
    GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness h1 h2
  have hsupp : (∑ a, (Δ a).ms) = Finset.univ.val.map fun i => (Δ i).first := by
    simp only [hms]
    rw [Finset.sum_eq_multiset_sum]
    exact Multiset.bind_singleton Finset.univ.val fun i => (Δ i).first
  rw [hsupp] at heq
  have hinj : Function.Injective fun D : Segment k => (D.first, D.len) := fun a b e =>
    Segment.ext_first (congrArg Prod.fst e) (congrArg Prod.snd e)
  have hm : 𝔪 = Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (unrChar k (α i))
      (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _) := by
    apply Multiset.map_injective hinj
    have e1 := congrArg (Multiset.map fun ρ : IrrGL k => (ρ, 1)) heq
    simp only [Multiset.map_map, Function.comp_def] at e1
    rw [← hord.1, Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def, hlen]
    exact e1
  rw [← hm]
  exact hL

end GlobalTheory.CompanionTheory.OneSat

open GlobalTheory.CompanionTheory.OneSat in

theorem GlobalTheory.CompanionTheory.OneSat.lOneSat : PositivityTheory.SphericalProduct.LOneSat := by
  intro k _ _ _ _ _ n ξ hξ V _ _ π hs
  have hϖ := valuation_unifU (k := k)
  have hms : ∀ (χ χ' : kˣ →* ℂˣ) (h : IsSmoothChar χ) (h' : IsSmoothChar χ') (c) (c'), χ = χ' →
      Segment.single (IrrGL.ofChar χ h) c = Segment.single (IrrGL.ofChar χ' h') c' := by
    rintro χ _ h h' c c' rfl; rfl
  have key : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL (Fin n) k) W), IsSmooth τ →
      HasSatake τ (PositivityTheory.SphericalProduct.atUnif k ξ) → IsL (PositivityTheory.SphericalProduct.msOne ξ hξ) τ := by
    intro W _ _ τ hτ hsat
    have φ := IrrGL.equivOf τ hτ hsat.1
    have h1 := isL_single_unrChar (IrrGL.of τ hτ hsat.1) (PositivityTheory.SphericalProduct.atUnif k ξ) (hasSatake_of_equiv φ hsat)
    have h2 : PositivityTheory.SphericalProduct.msOne ξ hξ = Finset.univ.val.map fun i : Fin n =>
        Segment.single (IrrGL.ofChar (unrChar k (PositivityTheory.SphericalProduct.atUnif k ξ i))
          (isSmoothChar_of_isUnram (isUnram_unrChar k _))) (IrrGL.isCusp_ofChar _ _) :=
      Multiset.map_congr rfl fun i _ => hms _ _ _ _ _ _ (eq_unrChar (hξ i) hϖ)
    rw [h2]
    exact h1.of_equiv φ.symm
  refine ⟨fun hL => ?_, key π hs⟩
  obtain ⟨y, hy⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake (k := k) (PositivityTheory.SphericalProduct.atUnif k ξ)
  have hLy := key y.ρ y.smooth hy
  obtain ⟨h, x, hd, hx, hc⟩ := hL
  have hc' := PositivityTheory.Exh.lOrderFree_of GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k _ h n x hd hx y.ρ hLy
  obtain ⟨e⟩ := hc.unique hc'
  exact hasSatake_of_equiv e hy

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeRankOneIsotropic
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.AvgZero

theorem avg_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) A < ⊤ ∧ ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (0 : Fv F v), ∀ V : Set (Fv F v), MeasurableSet V → V ⊆ U → |(coordW (Fv F v) b lam 1 M (A ∩ {X | algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) ∈ V})).toReal - (m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) A).toReal * (lam V).toReal| ≤ ε * (lam V).toReal := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM h₀ d b v lam hlam m hm A hAc hAo
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, htr, -, a8, -, a10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 1 M
  haveI : lam.IsAddHaarMeasure := hlam.1
  have hM1 : 1 ≤ M := by omega
  have hM2 : 2 ≤ M := by omega
  have hQ : Continuous fun X : Fin 1 → Fin M → Fv F v ⊗[F] E =>
      algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) :=
    continuous_const.mul (htr.comp ((a10 1 M J).matrix_elem 0 0))
  have hfam := GlobalTheory.T.rank_one_free_fibre_local F E σ hCM M J hJ d b v lam hlam m hm
  have hnull := GlobalTheory.T.local_dependent_set_null F E σ hCM M J hJ hM1 d b v lam hlam
  obtain ⟨ι, hι, P, u, hPc, hPo, hPZ, hsum, hcov⟩ :
      ∃ (ι : Type) (_ : Countable ι) (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (u : ι → (Fv F v ⊗[F] E)ˣ),
        IsCompact P ∧ IsOpen P ∧ P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧
        Summable (fun i => ‖Algebra.norm (Fv F v) (u i : Fv F v ⊗[F] E)‖₊ ^ (M - 1)) ∧
        A ∩ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ⊆
          ⋃ i, (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) =>
            (u i : Fv F v ⊗[F] E) * X p k) '' P := by
    by_cases hs : Nonempty (E →ₐ[F] Fv F v)
    · obtain ⟨τ⟩ := hs
      exact GlobalTheory.T.split_local_compact_cover_by_units F E σ hCM M hM2 v τ A hAc
    · exact GlobalTheory.T.local_compact_cover_by_unit_scalings F E σ hCM M hM2 v
        (GlobalTheory.CompanionTheory.DictLoc.isField_tensor_of_no_algHom hCM.2.2.1 (not_nonempty_iff.1 hs)) A hAc
  obtain ⟨c, hc⟩ := GlobalTheory.T.fibre_volume_compact_bound _ _ _ lam _ _ _ hQ hfam P hPc hPo hPZ
  have hset := fun i => GlobalTheory.T.unit_scaling_compact_free_set F E σ hCM M v (u i) P hPc hPo hPZ
  have hb := fun i S hS => GlobalTheory.T.local_rank_one_volume_bound F E σ hCM M J hJ hM1 d b v lam hlam P c hPo.measurableSet hc (u i) S hS
  have hmass := fun i => GlobalTheory.T.fibre_volume_compact_open_le_of_measure_le _ _ _ lam _ _ _ hQ hfam _ (hset i).1 (hset i).2.1 (hset i).2.2 _ (hb i)
  have key := GlobalTheory.T.fibre_volume_cover_countable _ _ ι _ lam _ _ _ hQ hfam hnull A hAc hAo _ _ hset hcov (hsum.mul_left c) hb hmass 0
  have e0 : hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀ = hermScal (Fv F v) σ 0 :=
    Subtype.ext (funext fun _ => funext fun _ => by
      show (1 : Fv F v) ⊗ₜ[F] (0 : E) = (0 : Fv F v) ⊗ₜ[F] (1 : E)
      simp)
  rw [e0]
  exact key

end GlobalTheory.CompanionTheory.SW.AvgZero
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeUnramifiedAlmostAllStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_volume_unramified_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)) m, μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree (Fv F v) σ J n μ ν m → ∀ h : HA (Fv F v) σ (blockOne (algebraMap F E t) J), m (hermOf (Fv F v) σ T hT) {X | actW (Fv F v) σ _ h (consTup X) ∈ latV b v} = (latV b v).indicator (fun _ => m (hermOf (Fv F v) σ T hT) (latV b v)) (actW (Fv F v) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageGoodFree.stage_good_free | exact GlobalTheory.CompanionTheory.SW.StageGoodFree.stage_good_free | (intros; apply GlobalTheory.CompanionTheory.SW.StageGoodFree.stage_good_free <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalWittIsotropicToE0Statement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_witt_isotropic_to_e0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ x : Fin 1 → Fin (M + 2) → R ⊗[F] E, LinearIndependent (R ⊗[F] E) x → gramR R σ (hypOne J) x = 0 → ∃ g : HA R σ (hypOne J), actW R σ (hypOne J) g (e0 _ M) = x := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypWitt.witt_e0 | exact GlobalTheory.CompanionTheory.WeilSiegel.HypWitt.witt_e0 | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypWitt.witt_e0 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableSetBox
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SigL

section Abstract

variable {M X : Type} [MeasurableSpace M] [MeasurableSpace X]

theorem abs_integral (f : M → X) (hf : Measurable f) {B : Set M} (hB : MeasurableSet B) (P : Measure M)
    (u : X → ℂ) (hu : AEStronglyMeasurable u ((P.restrict B).map f)) (Ξ : M → ℂ)
    (h1 : ∀ z ∈ B, Ξ z = u (f z)) (h2 : ∀ z, z ∉ B → Ξ z = 0) :
    (Integrable Ξ P → Integrable u ((P.restrict B).map f)) ∧ ∫ z, Ξ z ∂P = ∫ z, u z ∂((P.restrict B).map f) := by
  refine ⟨fun hi => ?_, ?_⟩
  · rw [integrable_map_measure hu hf.aemeasurable]
    refine (hi.integrableOn (s := B)).congr ?_
    filter_upwards [ae_restrict_mem hB] with z hz
    exact h1 z hz
  · rw [integral_map hf.aemeasurable hu, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B) h2]
    exact setIntegral_congr_fun hB h1

theorem abs_map (f : M → X) (hf : Measurable f) {B : Set M} (hB : MeasurableSet B) (P : Measure M)
    (T : M → M) (hT : Measurable T) (k : ℝ≥0) (Θ : X → X) (hΘ : Measurable Θ) (hBT : T ⁻¹' B = B)
    (hc : ∀ z, Θ (f z) = f (T z)) (hP : P.map T = k • P) :
    ((P.restrict B).map f).map Θ = k • (P.restrict B).map f := by
  rw [Measure.map_map hΘ hf]
  have e1 : Θ ∘ f = f ∘ T := funext hc
  rw [e1, ← Measure.map_map hf hT]
  have h1 : (P.restrict B).map T = k • P.restrict B := by
    have e2 := Measure.restrict_map (μ := P) hT hB
    rw [hBT, hP] at e2
    rw [← e2, Measure.restrict_smul]
  rw [h1, Measure.map_smul]

open Pointwise in
theorem abs_finite [AddCommGroup M] [TopologicalSpace M] [ContinuousAdd M] [TopologicalSpace X] [T2Space X]
    [OpensMeasurableSpace X] [OpensMeasurableSpace M] [T2Space M]
    (f : M → X) (hf : Measurable f) (ι : X → M) (hι : Continuous ι) {B : Set M} (hB : MeasurableSet B) (P : Measure M)
    [IsFiniteMeasureOnCompacts P] (T : Set M) (hT : IsCompact T) (h : ∀ z ∈ B, z - ι (f z) ∈ T) :
    IsFiniteMeasureOnCompacts ((P.restrict B).map f) := by
  refine ⟨fun C hC => ?_⟩
  have hCm : MeasurableSet C := hC.measurableSet
  have hK : IsCompact ((ι '' C) + T) := (hC.image hι).add hT
  rw [Measure.map_apply hf hCm, Measure.restrict_apply (hf hCm)]
  refine lt_of_le_of_lt (measure_mono ?_) hK.measure_lt_top
  rintro z ⟨hz, hzB⟩
  exact Set.mem_add.2 ⟨ι (f z), ⟨_, hz, rfl⟩, z - ι (f z), h z hzB, by abel⟩

theorem rh_one {A R : Type} [Ring A] [Ring R] (f : A →+* R) {e : A} (he : f e = 1) (y : A) : f ((1 - e) * y) = 0 := by
  rw [map_mul, map_sub, map_one, he, sub_self, zero_mul]

theorem rh_zero {A R : Type} [Ring A] [Ring R] (f : A →+* R) {e : A} (he : f e = 0) (y : A) : f ((1 - e) * y) = f y := by
  rw [map_mul, map_sub, map_one, he, sub_zero, one_mul]

theorem rh_map_zero {A R : Type} [Ring A] [Ring R] (f : A →+* R) : f 0 = 0 := map_zero f

end Abstract

end GlobalTheory.CompanionTheory.SigL

namespace GlobalTheory.CompanionTheory.SigL

variable {D : D7} {a b c r t : ℕ}

theorem topRing (D : D7) : IsTopologicalRing (AE D) :=
  isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)

def offS (S : Finset (Pl D)) : AddSubgroup (AE D) where
  carrier := {z | ∀ v ∉ S, cv D v z ∈ intLoc D.host.F D.host.E v}
  add_mem' := fun hx hy v hv => by rw [RingHom.map_add]; exact add_mem (hx v hv) (hy v hv)
  zero_mem' := fun v _ => by rw [RingHom.map_zero]; exact zero_mem _
  neg_mem' := fun hx v hv => by rw [RingHom.map_neg]; exact neg_mem (hx v hv)

theorem isOpen_offS (S : Finset (Pl D)) : IsOpen (offS S : Set (AE D)) := by
  haveI := topRing D
  have h0 : IsOpen {z : AE D | ∀ v : Pl D, cv D v z ∈ intLoc D.host.F D.host.E v} :=
    GlobalTheory.ThK.ConeEuler.UnitsOpen.isOpen_integral_everywhere
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (Filter.mem_of_superset (h0.mem_nhds ?_) ?_)
  · intro v
    rw [rh_map_zero]
    exact zero_mem _
  · intro z hz v _
    exact hz v

theorem isOpen_intOff (S : Finset (Pl D)) : IsOpen {x : Mx D a b | IntOff S x} := by
  have h : {x : Mx D a b | IntOff S x} = ⋂ i, ⋂ j, (fun x : Mx D a b => x i j) ⁻¹' (offS S : Set (AE D)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    exact ⟨fun h i j v hv => h v hv i j, fun h v hv i j => h i j v hv⟩
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_offS S).preimage (continuous_id.matrix_elem i j)

theorem measurableSet_box (S : Finset (Pl D)) :
    MeasurableSet {z : Mx D a r × Mx D a t | IntOff S z.1 ∧ IntOff S z.2} := by
  obtain ⟨g1, g2⟩ := top_pair (D := D) a r t
  have o : OpensMeasurableSpace (Mx D a r × Mx D a t) := g1.opensMeasurable
  exact (((isOpen_intOff S).preimage continuous_fst).inter ((isOpen_intOff S).preimage continuous_snd)).measurableSet

open Classical in

theorem exists_box (S : Finset (Pl D)) {e : AE D} (hS : IsIdem S e) (a b : ℕ) :
    ∃ T : Set (Mx D a b), IsCompact T ∧ ∀ x, IntOff S x → (1 - e) • x ∈ T := by
  have hL : ∀ v : Pl D, IsCompact (if v ∈ S then ({0} : Set (Fv D.host.F v ⊗[D.host.F] D.host.E))
      else (intLoc D.host.F D.host.E v : Set (Fv D.host.F v ⊗[D.host.F] D.host.E))) := fun v => by
    by_cases h : v ∈ S
    · rw [if_pos h]; exact isCompact_singleton
    · rw [if_neg h]; exact (GlobalTheory.ThK.isCompact_isOpen_intLoc v).1
  have hfin : ∀ᶠ v : Pl D in Filter.cofinite, (if v ∈ S then ({0} : Set (Fv D.host.F v ⊗[D.host.F] D.host.E))
      else (intLoc D.host.F D.host.E v : Set (Fv D.host.F v ⊗[D.host.F] D.host.E))) ⊆
        (intLoc D.host.F D.host.E v : Set (Fv D.host.F v ⊗[D.host.F] D.host.E)) := by
    refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
    by_contra h
    apply hv
    have h' : v ∉ S := h
    rw [if_neg h']
  obtain ⟨K, hK, hz⟩ := GlobalTheory.IdeleCyl.exists_isCompact_box D.host.F D.host.E (fun _ => {0}) _
    (fun _ => isCompact_singleton) hL hfin
  refine ⟨{x | ∀ i j, x i j ∈ K}, ?_, fun x hx i j => ?_⟩
  · have e1 : {x : Mx D a b | ∀ i j, x i j ∈ K} = Set.univ.pi fun _ => Set.univ.pi fun _ => K := by
      ext x
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    rw [e1]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK
  · refine hz _ (fun w => ?_) (fun v => ?_)
    · change compInf D.host.F D.host.E w ((1 - e) * x i j) ∈ ({0} : Set _)
      rw [rh_one _ (hS.1 w)]
      exact rfl
    · change cv D v ((1 - e) * x i j) ∈ _
      have hv := hS.2 v
      by_cases h : v ∈ S
      · rw [if_pos h] at hv
        rw [rh_one _ hv, if_pos h]
        exact rfl
      · rw [if_neg h] at hv
        rw [rh_zero _ hv, if_neg h]
        exact hx v h i j

theorem measurable_toX {e : AE D} (he : e * e = e) : Measurable (toX (a := a) (r := r) (t := t) he) := by
  haveI := topRing D
  obtain ⟨g1, g2⟩ := top_pair (D := D) a r t
  have o : OpensMeasurableSpace (Mx D a r × Mx D a t) := g1.opensMeasurable
  exact Measurable.subtype_mk
    ((continuous_fst.const_smul e).prodMk (continuous_snd.const_smul e)).measurable

end GlobalTheory.CompanionTheory.SigL
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NodeFunctionLeviDecompositionStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.node_function_levi_decomposition : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ), FlatFn e₁ → FlatFn e₂ → ∀ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (c : GL (Fin (r + s)) (Af E)), c ∈ KO E (r + s) → nodeFn e₁ e₂ (unip u * lev (Ad E) r s m * cf (r + s) k c) = e₁ m.1 * e₂ m.2 := by
  first | exact @GlobalTheory.CompanionTheory.LimV.NodeApply.nodeFn_apply | exact GlobalTheory.CompanionTheory.LimV.NodeApply.nodeFn_apply | (intros; apply GlobalTheory.CompanionTheory.LimV.NodeApply.nodeFn_apply <;> assumption)
end

