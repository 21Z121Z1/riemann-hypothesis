import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0002
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PairingExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0295
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0185
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0054
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchIntToZEqStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ToZPowCombIsometricStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ToZIsArithHeightIffStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0310
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0312
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0314
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0202
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.UnfSectionNormBoundAtHeightStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0046
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LineFnReadsLocalHeightSumStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LocalValuationLogNormsExistenceStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0275

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArFormExistsOfInt
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem arFormExists_of_int :
    (∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D →
      ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), ∃ Φ, IsArFun L D Φ) → GlobalTheory.Published.ArFormExists := by
  intro H k _ X _ p D hX ι _ L
  let t : X ⟶ Sp ℤ := specZIsTerminal.from X
  haveI : Module.Finite ℤ k := hX.finite
  have hL : ∀ i τ, (wZ (L i) t τ).IsCInf := fun i τ => GlobalTheory.T.wZ_isCInf' k X p t (L i) τ
  obtain ⟨Φ, hΦ⟩ := H X t D (GlobalTheory.CompanionTheory.Ar.BaseZ.isArithVar_int k X p t D hX) ι
    (fun i => GlobalTheory.CompanionTheory.Ar.BaseZ.toZ (L i) t (hL i))
  exact ⟨Φ, (GlobalTheory.T.toZ_isArFun_iff k X p t D hX ι L hL Φ).1 hΦ⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArMixOfBaseInt
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem arMix_of_base_int : (∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D → ∀ (ι : Type) [Fintype ι] (M : HermLB p) (L : ι → HermLB p) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ), IsArFun (fun o : Option ι => o.elim M L) D Φ → ∀ (n : ι → ℤ) (h : X → ℝ), (comb L n).IsArithHeight h → ∀ (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (comb L n).ArchIntegrable M D hr ∧ Φ (MvPolynomial.X none * MvPolynomial.rename some (lin fun i => (n i : ℝ)) ^ D) = ∑ᶠ z, ((M.div hr).mult z : ℝ) * h z - (comb L n).archInt M D hr) → GlobalTheory.Published.ArMix := by
  intro H k _ X _ _ p D hX ι _ M L Φ hΦ n h hh r hr
  haveI := hX.finite
  let t : X ⟶ Sp ℤ := p ≫ spMap (Int.castRingHom k)
  have hX' : IsArithVar t D := isArithVar_int k X p t D hX
  have Hc : ∀ (N : HermLB p) (τ : ℤ →+* ℂ), (wZ N t τ).IsCInf := fun N τ => GlobalTheory.T.wZ_isCInf' k X p t N τ
  have hΦ' : IsArFun (fun o : Option ι => o.elim (toZ M t (Hc M)) fun i => toZ (L i) t (Hc (L i))) D Φ := by
    have e := (GlobalTheory.T.toZ_isArFun_iff k X p t D hX (Option ι) (fun o : Option ι => o.elim M L)
      (fun o => Hc _) Φ).2 hΦ
    convert e using 2 with o
    cases o <;> rfl
  have iso : (toZ (comb L n) t (Hc _)).Isometric (comb (fun i => toZ (L i) t (Hc (L i))) n) :=
    (GlobalTheory.T.toZ_pow_comb_isometric k X p t Hc).2 ι L n
  have hh' : (comb (fun i => toZ (L i) t (Hc (L i))) n).IsArithHeight h :=
    iso.isArithHeight hX' ((GlobalTheory.T.toZ_isArithHeight_iff k X p t D hX (comb L n) (Hc _) h).2 hh)
  obtain ⟨h₁, h₂⟩ := H X t D hX' ι (toZ M t (Hc M)) (fun i => toZ (L i) t (Hc (L i))) Φ hΦ' n h hh' r hr
  have hA : (toZ (comb L n) t (Hc _)).ArchIntegrable (toZ M t (Hc M)) D hr := fun τ => by
    rw [iso.chernIntegrableOn_eq]
    exact h₁ τ
  have hI : (comb (fun i => toZ (L i) t (Hc (L i))) n).archInt (toZ M t (Hc M)) D hr =
      (toZ (comb L n) t (Hc _)).archInt (toZ M t (Hc M)) D hr := by
    simp only [HermLB.archInt, iso.chernInt_eq]
  obtain ⟨e₁, e₂⟩ := GlobalTheory.T.archInt_toZ_eq k X p t D hX (comb L n) M (Hc _) (Hc _) D r hr
  have hB := e₁.1 hA
  refine ⟨hB, h₂.trans ?_⟩
  rw [hI, e₂ hB]
  rfl

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsConstSectionKroneckerChar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br.CovEx

theorem exists_padic_emb (K : Type) [Field K] [NumberField K] (p : Nat.Primes) : Nonempty (K →+* ℂ_[p]) := by
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  exact ⟨(IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ_[p]) : K →ₐ[ℚ] ℂ_[p]).toRingHom⟩

theorem goodOf_or {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (σ : c.F →+* ℂ) : Formalism.L2.Pj.goodOf c σ = σ ∨ (starRingEnd ℂ).comp (Formalism.L2.Pj.goodOf c σ) = σ := by
  unfold Formalism.L2.Pj.goodOf
  split_ifs
  · exact Or.inl rfl
  · right; ext x; simp

theorem exists_constSec : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (r : ℕ)
    (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r) (x : ℝ), GlobalTheory.FlatCore.Laws U x → ∀ [NeZero H.d]
    (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (Z : Formalism.L2.Pj.Comp Xo c) (τ : GlobalTheory.AllWt.Psi H),
    ∃ s : GlobalTheory.FlatLine.ConstSec U x Z (GlobalTheory.FlatLine.flatWt D τ) 0,
      s.deg = ((D.p : ℝ) - D.q) / 2 * (GlobalTheory.CM.logOm E χ).re := by
  intro hR hG E _ _ _ H D l Xo c r U x hL _ χ hχ Z τ
  have hpos := hL.pos
  obtain ⟨κ⟩ := exists_padic_emb c.F (⟨2, Nat.prime_two⟩ : Nat.Primes)
  obtain ⟨O, _, _, _, β, Y, hβ, -, -, -⟩ :=
    GlobalTheory.T.good_reduction_dvr_model_exists E H D l Xo c ⟨2, Nat.prime_two⟩ κ hpos (hL.good 2 Nat.prime_two)
  obtain ⟨hclopen, hcpt, -⟩ := GlobalTheory.T.irreducible_component_clopen E H D l Xo c (Z : Set (Xo.XF c)) Z.2
  obtain ⟨Z'⟩ := hcpt O β Y hβ
  have hgeom : Z'.IsGeom := GlobalTheory.T.geometric_component_alg_closed E H D l Xo c O β Y Z Z' hβ hL.geo
  obtain ⟨φ, hline, hflat, -⟩ := GlobalTheory.T.flat_zero_from_resolution_and_gaga hR hG E H D l Xo c O β Y Z Z' τ.1 hβ hpos τ.2 hgeom
  obtain ⟨hnorm, -⟩ := GlobalTheory.T.flat_first_from_resolution_and_gaga hR hG E H D l Xo c O β Y Z Z' τ.1 φ hβ hpos τ.2 hgeom hline hflat
  choose t ht ht' using fun σ => hnorm (Formalism.L2.Pj.goodOf c σ)
  have hInf : ∀ σ, HasInfNorm (Z : Set (Xo.XF c)) τ.1 φ σ (t σ) := fun σ => by
    rcases goodOf_or c σ with h | h
    · have := ht σ
      rwa [h] at this
    · have := ht' σ
      rwa [h] at this
  have hFinEx : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm (Z : Set (Xo.XF c)) τ.1 φ p κ t :=
    fun p κ => GlobalTheory.T.frame_function_finite_norm hR hG E H D l Xo c O β Y Z Z' τ.1 φ p κ hβ hpos τ.2 Z.2 hgeom hflat (hL.good p p.2)
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.finite_norm_local_bound E H D l Xo c Z τ.1 φ hFinEx
  obtain ⟨hex, ⟨N, hNinf, hNfin⟩, hdict⟩ := GlobalTheory.T.local_valuation_log_norms_existence c.F (fun σ => Real.exp (t σ)) ρ
  have hinfN : ∀ s, HasInfNorm (Z : Set (Xo.XF c)) τ.1 φ s (N.inf s) := fun s => by
    rw [hNinf s, Real.log_exp]
    exact hInf s
  have hfinN : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm (Z : Set (Xo.XF c)) τ.1 φ p κ (N.fin p κ) :=
    fun p κ => by
      obtain ⟨la, π, h1, h2⟩ := hex p κ
      rw [hNfin p κ la π h1 h2]
      exact hρ p κ la π h1 h2
  obtain ⟨hadel, hdeg⟩ := GlobalTheory.T.kronecker_character_frame_bound hR hG E H D l Xo c O β Y _ Z' τ.1 φ N χ hχ hβ hpos τ.2 hclopen hgeom hflat
    hinfN hfinN
  obtain ⟨hsupp, hline'⟩ := hdict N hNinf hNfin
  obtain ⟨s, s', hs, hs', hi, hi', hm, hread⟩ := GlobalTheory.T.flat_on_model_exists_rul_sections E H D l Xo c O β Y Z Z' τ φ hflat
  have hval := GlobalTheory.T.line_fn_reads_local_height_sum E H D l Xo c Z τ s φ ρ hline hread hρ
  have hPts := GlobalTheory.FlatLine.hasPts U hpos hL.good hL.unf Z
  refine ⟨{ sig := s, inv := s', sig_mem := hs, inv_mem := hs', idem_sig := hi, idem_inv := hi', mul_inv := hm,
            cInf := fun σ => Real.exp (t σ), cInf_pos := fun σ => Real.exp_pos _,
            norm_inf := fun σ => GlobalTheory.FlatLine.image_eq_singleton_iff.2 ⟨(hPts.1 σ).1, fun z hz =>
              GlobalTheory.T.unf_section_norm_bound_at_height E H D l Xo c r (Formalism.L2.Pj.goodOf c σ) (U (Formalism.L2.Pj.goodOf c σ)) x Z τ s φ (t σ)
                (Formalism.L2.Pj.goodEmb_goodOf c σ) (hL.unf _ (Formalism.L2.Pj.goodEmb_goodOf c σ))
                (hL.xi _ (Formalism.L2.Pj.goodEmb_goodOf c σ)) hs hline hread (ht σ) z hz ((hPts.1 σ).2 z hz)⟩,
            rho_vw := ρ,
            val_fin := fun w => GlobalTheory.FlatLine.image_eq_singleton_iff.2 ⟨hPts.2 w, fun v hv => by
              simpa using hval w v hv⟩,
            finite_rho := hsupp.1 hadel }, ?_⟩
  exact (hline' hadel).symm.trans hdeg

end GlobalTheory.CompanionTheory.Ar.Br.CovEx
end
end

