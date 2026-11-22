import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SectionBaseChangeOfBasis
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0063
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0013
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0080
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0011
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0016
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0037
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0008
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0025
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ActLevAndActBC
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldBC

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
  Formalism.BasicNotions

theorem actLev_of_le {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {G : Type} [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La))
    (hL : ActLev (Xo := Xo) c lev) : ActLev (Xo := Xo) c' lev := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g S _ _ y
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    obtain ⟨z, hz⟩ := hL.total g S (y.res hle h)
    exact ⟨z.ext hle h, hz⟩
  · intro g S _ _ y y₁ y₂ h₁ h₂
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    exact hL.func g S (y.res hle h) (y₁.res hle h) (y₂.res hle h) h₁ h₂
  · intro S _ _ y
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    exact hL.one S (y.res hle h)
  · intro g g' S _ _ y y₁ y₂ h₁ h₂
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    exact hL.mul g g' S (y.res hle h) (y₁.res hle h) (y₂.res hle h) h₁ h₂
  · intro g S T _ _ _ _ φ y y' z z' h₀ h₁ h₂
    letI := resAlg hle S
    letI := resAlg hle T
    have hS : AlgOver c c' hle S := fun _ => rfl
    have hT : AlgOver c c' hle T := fun _ => rfl
    let ψ : S →ₐ[c.F] T := { φ.toRingHom with commutes' := fun x => φ.commutes _ }
    exact hL.nat g S T ψ (y.res hle hS) (y'.res hle hS) (z.res hle hT) (z'.res hle hT) h₀ h₁ h₂
  · intro g S _ _ t y y' z z' h₀ h₁ h₂
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    exact hL.bor g S t (y.res hle h) (y'.res hle h) (z.res hle h) (z'.res hle h) h₀ h₁ h₂

theorem actLev_and_actBC (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (G : Type) [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La))
    (hL : ActLev (Xo := Xo) c lev) :
    ActLev (Xo := Xo) c' lev ∧ ActBC hle (actLev (Xo := Xo) c lev) (actLev (Xo := Xo) c' lev) :=
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hc := fun c => GlobalTheory.Frames.chartCoverF_of_secBaseChange hS D.host.E H Dw l Xo c
  ⟨actLev_of_le hle lev hL, actBC_of hle lev (evalWD_fr (frChartF_of (hc c))) (evalWD_fr (frChartF_of (hc c'))) hL
    (actLev_of_le hle lev hL)⟩

end GlobalTheory.FieldBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjugateSectionValuesSemilinear
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.GalTw

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CoefChangeCompare (Natural FromT ValueWD map_trans evR_spec evR_not evR_map)

namespace Rule

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {ta : c.F ≃+* c.F}

theorem fixes_symm (h : Fixes c ta) : Fixes c ta.symm :=
  ⟨fun τ a => by rw [RingEquiv.symm_apply_eq, h.emb], fun a => by rw [RingEquiv.symm_apply_eq, h.base]⟩

def twHom (ta : c.F ≃+* c.F) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) : Tw ta S →ₐ[c.F] Tw ta T :=
  { φ.toRingHom with commutes' := fun a => φ.commutes (ta a) }

def untwHom {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] Tw ta T) : Tw ta.symm S →ₐ[c.F] T :=
  { φ.toRingHom with
    commutes' := fun a => (φ.commutes (ta.symm a)).trans
      (congrArg (algebraMap c.F T) (ta.apply_symm_apply a)) }

theorem fromT_tw_test (h : Fixes c ta) (hA : AllTest Xo c) (p : TRing c.F) (y : FrPt Xo c p.R) :
    FromT (twPt h y) := by
  haveI : IsReduced (Tw ta p.R) := ((GlobalTheory.reduced_finiteType_iff_testRing c.F).2 p).2
  exact hA _ _

theorem fromT_of_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (hy : FromT y) (hm : FrMap φ y z) : FromT z := by
  obtain ⟨p, ψ, y₀, h₀⟩ := hy
  exact ⟨p, _, y₀, map_trans ψ φ h₀ hm⟩

theorem frMap_tw (h : Fixes c ta) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (hm : FrMap φ y z) :
    FrMap (twHom ta φ) (twPt h y) (twPt h z) := hm

theorem fromT_of_tw (h : Fixes c ta) (hA : AllTest Xo c) {S : Type} [CommRing S] [Algebra c.F S]
    {y : FrPt Xo c S} (hy : FromT (twPt h y)) : FromT y := by
  obtain ⟨p, φ, y₀, h₀⟩ := hy
  have h₁ : FrMap (untwHom φ) (twPt (fixes_symm h) y₀) y := h₀
  exact fromT_of_map (fromT_tw_test (fixes_symm h) hA p y₀) h₁

theorem evR_galRul (h : Fixes c ta) (hWD : ValueWD Xo c) (hA : AllTest Xo c) {f : Rul Xo c} (hf : Natural c f)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    evR Xo c (galRul h f) y = (evR Xo c f (twPt h y)).val := by
  by_cases hy : FromT y
  · obtain ⟨q, φ, y₀, hm, e⟩ := evR_spec hy
    rw [e, evR_map hWD hf (fromT_tw_test h hA q y₀) (frMap_tw h hm)]
    rfl
  · rw [evR_not hy, evR_not (fun h' => hy (fromT_of_tw h hA h'))]
    rfl

theorem galRul_mem_sec (h : Fixes c ta) (hWD : ValueWD Xo c) (hA : AllTest Xo c) (hB : BorChartF Xo c)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) : galRul h f ∈ sec Xo c a n := by
  refine ⟨fun p q φ y z hm => ?_, fun q t y y' hb => ?_⟩
  · exact evR_map hWD hf.1 (fromT_tw_test h hA p y) (frMap_tw h hm)
  · have hb' : FrBor (S := Tw ta q.R) t (twPt h y) (twPt h y') := hb
    have h3 : evR Xo c f (twPt h y') = _ * evR Xo c f (twPt h y) :=
      wtAll_of_borChart hB (ex Dw a n) hf.1 hf.2 (Tw ta q.R) _ _ _ (fromT_tw_test h hA q y)
        (fromT_tw_test h hA q y') hb'
    exact h3

end Rule

theorem galRul_sec_val_semilinear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, galRul h f ∈ sec Xo c a n ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), evR Xo c (galRul h f) y = (evR Xo c f (twPt h y)).val) ∧ (∀ (t : c.F) (f g : Rul Xo c), galRul h (t • f + g) = ta t • galRul h f + galRul h g) ∧ ∀ (c₀ : Coeff l) (hle : c₀.F ≤ c.F), (∀ x : c₀.F, ta (incF c₀ c hle x) = incF c₀ c hle x) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (as : Fin m → c.F) (fs : Fin m → Rul Xo c₀), ∀ f ∈ sec Xo c a n, IsBC hle f as fs → IsBC hle (galRul h f) (fun i => ta (as i)) fs := by
  intro E _ _ _ H Dw l Xo c ta h
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hc := GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c
  have hWD : ValueWD Xo c := evalWD_fr (frChartF_of hc)
  have hA : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  have hB : BorChartF Xo c := borChartF_of_cover hc
  refine ⟨fun a n f hf => ⟨Rule.galRul_mem_sec h hWD hA hB hf, fun S _ _ y => Rule.evR_galRul h hWD hA hf.1 y⟩,
    fun t f g => ?_, ?_⟩
  · funext p y
    have h1 : evR Xo c (t • f + g) (twPt h y) =
        algebraMap c.F (Tw ta p.R) t * evR Xo c f (twPt h y) + evR Xo c g (twPt h y) := by
      unfold evR
      rw [evalAt_add, evalAt_smul]
    refine h1.trans ?_
    show _ = ta t • galRul h f p y + galRul h g p y
    rw [Algebra.smul_def]
    rfl
  · intro c₀ hle hfix a n m as fs f hf hbc S _ A _ ho y
    letI : Algebra c₀.F (Tw ta S) := A
    have ho' : AlgOver c₀ c hle (Tw ta S) := fun x =>
      (congrArg (algebraMap c.F S) (hfix x)).trans (ho x)
    rw [Rule.evR_galRul h hWD hA hf.1 y]
    exact hbc (Tw ta S) ho' (twPt h y)

end GlobalTheory.GalTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqOfForallAlgClosed
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory.ClassSumUnique

theorem eq_of_forall_algClosed {K R : Type} [Field K] [CommRing R] [Algebra K R] [IsReduced R] (u v : R)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : R →ₐ[K] k), φ u = φ v) : u = v := by
  rw [← sub_eq_zero]
  refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun J hJ => ?_)
  let ψ : R →+* AlgebraicClosure J.ResidueField :=
    (algebraMap J.ResidueField (AlgebraicClosure J.ResidueField)).comp (algebraMap R J.ResidueField)
  letI : Algebra K (AlgebraicClosure J.ResidueField) := (ψ.comp (algebraMap K R)).toAlgebra
  have e : ψ u = ψ v := h (AlgebraicClosure J.ResidueField) { ψ with commutes' := fun _ => rfl }
  have e' : algebraMap R J.ResidueField u = algebraMap R J.ResidueField v :=
    (algebraMap J.ResidueField (AlgebraicClosure J.ResidueField)).injective e
  rw [← Ideal.algebraMap_residueField_eq_zero, map_sub, e', sub_self]

theorem sec_eq_of_geometric {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {a : (E →+* ℂ) × ℕ → ℕ} {m : ℕ} {f f' : Rul Xo c} (hf : f ∈ sec Xo c a m)
    (hf' : f' ∈ sec Xo c a m)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k), evR Xo c f y = evR Xo c f' y) :
    f = f' := by
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hWD : GlobalTheory.CoefChangeCompare.ValueWD Xo c :=
    evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c))
  have hBC : GlobalTheory.CoefChangeCompare.HasBC Xo c := GlobalTheory.CoefChangeCompare.hasBC_of hS
  funext p y
  haveI := ((GlobalTheory.reduced_finiteType_iff_testRing c.F).2 p).2
  refine eq_of_forall_algClosed (K := c.F) _ _ fun k _ _ _ φ => ?_
  obtain ⟨z, hz⟩ := hBC p.R k φ y
  rw [← GlobalTheory.CoefChangeCompare.evR_of_map hWD hf.1 hz, ← GlobalTheory.CoefChangeCompare.evR_of_map hWD hf'.1 hz]
  exact h k z

theorem isThClsD_unique : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F), d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → (∀ k, (La k).Unimod ∧ (La k).TrivAt d.l₂.M ∧ (La k).LevOK (Nc k) d.l₂.M) → ∀ (a : (E →+* ℂ) × ℕ → ℕ), (∀ v, io v ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ (x : Cl → Vs) (a' : (E →+* ℂ) × ℕ → ℕ) (m : ℕ), ∀ f ∈ sec Xo c a' m, ∀ f' ∈ sec Xo c a' m, IsThClsD Xo c d w La Nc gam vol ep io x f → IsThClsD Xo c d w La Nc gam vol ep io x f' → f = f' := by
  intro hC E _ _ _ H Dw l Xo c n d Cl _ w La Nc gam vol ep Vs _ _ io hd hnab hLa a hio x a' m f hf f' hf' h h'
  obtain ⟨_, hnab⟩ := hnab
  refine sec_eq_of_geometric hf hf' fun k _ _ _ y => ?_
  letI : Algebra d.c₂.F k := ((algebraMap c.F k).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
  have hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a => by
    show algebraMap c.F k (d.eF.symm (d.eF a)) = _
    rw [AlgEquiv.symm_apply_apply]
  obtain ⟨y₂, hy⟩ := hd.2.2.2.2.2.2.1 k hk y
  obtain ⟨v, hv, e⟩ := h k hk y y₂ hy
  obtain ⟨v', hv', e'⟩ := h' k hk y y₂ hy
  have hvv : v = v' := funext fun cl =>
    ((GlobalTheory.shortThetaValue_existsUnique_natural GlobalTheory.abelianSchemeLaws_all.1 hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n
      (La cl) (Nc cl) (hLa cl).1 (hLa cl).2.1 (hLa cl).2.2 a _
      ((GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a _ (hio (x cl))) (fun q => d.eF (w cl q)) 1).1 k y₂).unique
      (hv cl) (hv' cl)
  rw [e, e', hvv]

end GlobalTheory.ClassSumUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBaseEmbeddingReadingFormsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_embedding_reading_forms : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)), ∃ (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e := by
  first | exact @GlobalTheory.Shares.exists_isRdgU | exact GlobalTheory.Shares.exists_isRdgU | (intros; apply GlobalTheory.Shares.exists_isRdgU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsHomogeneousAevalEqZero
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.SecRelation

theorem coeff_aeval_C_mul_X {K Ω σ : Type} [Field K] [Field Ω] [Algebra K Ω] [Fintype σ] (v : σ → Ω)
    (P : MvPolynomial σ K) (d : ℕ) :
    (MvPolynomial.aeval (fun i => Polynomial.C (v i) * Polynomial.X) P).coeff d =
      MvPolynomial.aeval v (MvPolynomial.homogeneousComponent d P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    have h : MvPolynomial.aeval (fun i => Polynomial.C (v i) * Polynomial.X) (MvPolynomial.monomial s a) =
        Polynomial.C (MvPolynomial.aeval v (MvPolynomial.monomial s a)) * Polynomial.X ^ s.degree := by
      rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, Finsupp.prod, Finsupp.prod]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow,
        Polynomial.algebraMap_apply, Finsupp.degree_apply, mul_assoc]
    rw [h, Polynomial.coeff_C_mul_X_pow,
      MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial a rfl)]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]

theorem exists_isHomogeneous_aeval_eq_zero {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}
    (hD : Algebra.trdeg K Ω = D) (hm : D + 2 ≤ m) (v : Fin m → Ω) :
    ∃ (Q : MvPolynomial (Fin m) K) (d : ℕ), Q ≠ 0 ∧ Q.IsHomogeneous d ∧ MvPolynomial.aeval v Q = 0 := by
  have htr : Algebra.trdeg K (Polynomial Ω) = ((D + 1 : ℕ) : Cardinal) := by
    rw [← trdeg_add_eq K Ω (A := Polynomial Ω), Polynomial.trdeg_of_isDomain, hD]
    push_cast
    rfl
  have hdep : ¬ AlgebraicIndependent K (fun i => Polynomial.C (v i) * Polynomial.X) := by
    intro h
    have h1 := h.cardinalMk_le_trdeg
    rw [htr, Cardinal.mk_fin, Nat.cast_le] at h1
    omega
  rw [algebraicIndependent_iff] at hdep
  push_neg at hdep
  obtain ⟨P, hP, hP0⟩ := hdep
  have hex : ∃ d, MvPolynomial.homogeneousComponent d P ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hP0
    rw [← MvPolynomial.sum_homogeneousComponent P]
    exact Finset.sum_eq_zero fun d _ => hall d
  obtain ⟨d, hd⟩ := hex
  refine ⟨_, d, hd, MvPolynomial.homogeneousComponent_isHomogeneous d P, ?_⟩
  rw [← coeff_aeval_C_mul_X, hP, Polynomial.coeff_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem one_mem_sec : (1 : Rul Xo c) ∈ sec Xo c 0 0 := by
  refine ⟨fun p q φ y z _ => ?_, fun p t y y' _ => ?_⟩
  · show (1 : q.R) = φ 1
    rw [map_one]
  · show (1 : p.R) = wchar (ex Dw 0 0) t * 1
    have : ex Dw (0 : (E →+* ℂ) × ℕ → ℕ) 0 = fun _ => 0 := by funext i; cases i <;> rfl
    simp [wchar, this]

theorem multiset_prod_mem_sec {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {σ : Type} (u : σ → Rul Xo c)
    (hu : ∀ i, u i ∈ sec Xo c a n) (s : Multiset σ) :
    (s.map u).prod ∈ sec Xo c (s.card • a) (s.card • n) := by
  induction s using Multiset.induction_on with
  | empty => simpa using one_mem_sec
  | cons i s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, succ_nsmul', succ_nsmul']
    exact sec_mul Xo c _ _ _ _ (hu i) ih

theorem aeval_mem_sec {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {σ : Type} (u : σ → Rul Xo c)
    (hu : ∀ i, u i ∈ sec Xo c a n) {Q : MvPolynomial σ c.F} {d : ℕ} (hQ : Q.IsHomogeneous d) :
    MvPolynomial.aeval u Q ∈ sec Xo c (d • a) (d • n) := by
  classical
  rw [Q.as_sum, map_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  have hc : s.toMultiset.card = d := by
    rw [Finsupp.card_toMultiset]
    have := hQ (MvPolynomial.mem_support_iff.1 hs)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have h1 := multiset_prod_mem_sec u hu s.toMultiset
  rw [hc, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (by simp) (by intros; rw [pow_add])] at h1
  rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ h1

theorem exists_algHom_evR {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) :
    ∃ ψ : Rul Xo c →ₐ[c.F] S, ∀ f, evR Xo c f y = ψ f :=
  ⟨AlgHom.ofLinearMap (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y)
    (evalAt_one _ _ y h) (fun f g => evalAt_mul _ _ f g y), fun _ => rfl⟩

theorem exists_homogeneous_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ), Module.finrank ℚ E / 2 * (Dw.p * Dw.q + Dw.p * (Dw.p - 1) / 2 + Dw.q * (Dw.q - 1) / 2) + 2 ≤ m → ∀ u : Fin m → Rul Xo c, (∀ i, u i ∈ sec Xo c a n) → ∃ (Q : MvPolynomial (Fin m) c.F) (d : ℕ), Q ≠ 0 ∧ Q.IsHomogeneous d ∧ MvPolynomial.aeval u Q = 0 := by
  intro E _ _ _ H Dw l Xo c a n m hm u hu
  classical
  obtain ⟨hL, -, h, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have htr := (GlobalTheory.FlagDim.fnFG_fnTrdeg E H Dw l Xo c).2
  haveI := CompFin.finite_comp Xo c
  haveI : Fintype (Comp Xo c) := Fintype.ofFinite _
  choose Q d hQ0 hQd hQv using fun Z : Comp Xo c =>
    exists_isHomogeneous_aeval_eq_zero (htr Z) hm (fun i => evC h Z (u i))
  have hhom : (∏ Z, Q Z).IsHomogeneous (∑ Z, d Z) := MvPolynomial.IsHomogeneous.prod _ _ _ fun Z _ => hQd Z
  refine ⟨∏ Z, Q Z, ∑ Z, d Z, Finset.prod_ne_zero_iff.2 fun Z _ => hQ0 Z, hhom, ?_⟩
  refine GlobalTheory.Reg.sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) _ _ _ (aeval_mem_sec u hu hhom) fun Z => ?_
  obtain ⟨ψ, hψ⟩ := exists_algHom_evR (genFr h Z) (hL.test _ _)
  have h1 : ψ (MvPolynomial.aeval u (Q Z)) = 0 := by
    rw [← hQv Z, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    exact congrArg (fun v => MvPolynomial.aeval v (Q Z)) (funext fun i => (hψ (u i)).symm)
  show evR Xo c _ (genFr h Z) = 0
  rw [hψ, map_prod, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ Z) h1

end GlobalTheory.SecRelation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NoCommonZeroOfReadings
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FrameZero

theorem exists_complex_point {K A : Type} [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (σ : K →+* ℂ) (I : Ideal A) (hI : I ≠ ⊤) : ∃ ψ : A →ₐ[K] CAt σ, ∀ x ∈ I, ψ x = 0 := by
  classical
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  haveI := hM
  letI : Field (A ⧸ M) := Ideal.Quotient.field M
  letI : Algebra K ℂ := σ.toAlgebra
  haveI : Module.Finite K (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ M)
  let g : (A ⧸ M) →ₐ[K] ℂ := IsAlgClosed.lift
  let f : A →ₐ[K] ℂ := g.comp (Ideal.Quotient.mkₐ K M)
  refine ⟨⟨(f : A →+* ℂ), fun r => f.commutes r⟩, fun x hx => ?_⟩
  show g (Ideal.Quotient.mk M x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hIM hx), map_zero]

set_option synthInstance.maxHeartbeats 400000 in

theorem noCommonZero_of_readings : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → T.R j), (∀ i, ws i ∈ sec (T.Q.Xo j) T.Q.c a n) → (∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, ∃ i, rdU (T.U j T.σ₀) (ws i) k x ≠ 0) → NoCommonZero (T.Q.Xo j) T.Q.c ws := by
  intro D T h j hj a n m ws hws hz
  obtain ⟨hL, -, hG, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c
  have hu := (h.toLawsCore.unf j hj T.σ₀ T.good_σ₀).2.2.1
  intro k _ _ _ y
  by_contra hne
  simp only [not_exists, not_not] at hne
  obtain ⟨C, ψ, z, t', hψ, hbor⟩ := hA hG k y
  have hz0 : ∀ i, evR (T.Q.Xo j) T.Q.c (ws i) z = 0 := by
    intro i
    have e1 := GlobalTheory.ArcQ.evR_frBor_of_isDomain hL (hws i) t' z y hbor
    rw [hne i] at e1
    have hw : wchar (ex (T.Q.Dw j) a n) t' ≠ 0 := by
      unfold wchar
      exact Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (Units.ne_zero _)
    exact (mul_eq_zero.mp e1.symm).resolve_left hw
  have hsm := C.sm
  have hI : Ideal.span (Set.range fun i => evR (T.Q.Xo j) T.Q.c (ws i) C.y) ≠ ⊤ := by
    intro htop
    have hker : Ideal.span (Set.range fun i => evR (T.Q.Xo j) T.Q.c (ws i) C.y) ≤ RingHom.ker ψ := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker,
        ← GlobalTheory.Reg.evR_baseChange_of_isReduced _ _ _ _ (T.Q.Xo j) T.Q.c hL a n (ws i) (hws i) _ k ψ C.y z hψ]
      exact hz0 i
    have h1 := hker (htop ▸ Submodule.mem_top : (1 : C.R) ∈ _)
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  obtain ⟨ψ', hψ'⟩ := exists_complex_point T.σ₀ _ hI
  obtain ⟨z', hz'⟩ := hL.bc _ _ ψ' C.y
  obtain ⟨kk, x, t, hb⟩ := hu z'
  obtain ⟨i, hi⟩ := hz kk x.1 x.2
  apply hi
  haveI : IsDomain (CAt T.σ₀) := inferInstanceAs (IsDomain ℂ)
  have e2 := GlobalTheory.ArcQ.evR_frBor_of_isDomain hL (hws i) t _ _ hb
  have e3 := GlobalTheory.Reg.evR_baseChange_of_isReduced _ _ _ _ (T.Q.Xo j) T.Q.c hL a n (ws i) (hws i) _ _ ψ' C.y z' hz'
  have e4 : ψ' (evR (T.Q.Xo j) T.Q.c (ws i) C.y) = 0 := hψ' _ (Ideal.subset_span ⟨i, rfl⟩)
  have hw2 : wchar (ex (T.Q.Dw j) a n) t ≠ 0 := by
    unfold wchar
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (Units.ne_zero _)
  have e6 : wchar (ex (T.Q.Dw j) a n) t * evR (T.Q.Xo j) T.Q.c (ws i) ((T.U j T.σ₀).un kk x) = 0 := by
    rw [← e2, e3, e4]
  have e5 := (mul_eq_zero.mp e6).resolve_left hw2
  unfold rdU
  simp only [LinearMap.coe_mk, AddHom.coe_mk, dif_pos x.2, e5]
  unfold toC
  rfl

end GlobalTheory.FrameZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.FieldBC

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CoefChangeCompare (ValueWD HasBC hasBC_of ruleUp_mem_sec evR_ruleUp)

theorem rulBC_sec_val_linear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F), (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, rulBC hle f ∈ sec Xo c' a n ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S), evR Xo c' (rulBC hle f) y = evR Xo c f (y.res hle h)) ∧ (∀ (t : c.F) (f g : Rul Xo c), rulBC hle (t • f + g) = incF c c' hle t • rulBC hle f + rulBC hle g) := by
  intro E _ _ _ H Dw l Xo c c' hle
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hWD : ValueWD Xo c :=
    evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c))
  have hBC : HasBC Xo c := hasBC_of hS
  refine ⟨fun a n f hf => ⟨ruleUp_mem_sec hle hWD hBC hf, ?_⟩, fun t f g => ?_⟩
  · intro S _ A _ h y
    obtain rfl : A = resAlg hle S := Algebra.algebra_ext _ _ fun x => (h x).symm
    exact evR_ruleUp hle hWD hBC hf.1 y
  · funext p y
    letI := resAlg hle p.R
    have h1 : evR Xo c (t • f + g) (y.res hle (fun _ => rfl)) =
        algebraMap c.F p.R t * evR Xo c f (y.res hle (fun _ => rfl)) + evR Xo c g (y.res hle (fun _ => rfl)) := by
      unfold evR
      rw [evalAt_add, evalAt_smul]
    refine h1.trans ?_
    show _ = incF c c' hle t • rulBC hle f p y + rulBC hle g p y
    rw [Algebra.smul_def]
    rfl

end GlobalTheory.FieldBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SecBCAndCuspBC
section
set_option autoImplicit false

namespace GlobalTheory.FieldBC

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem secBC_and_cuspBC (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) :
    SecBC Xo hle ∧ ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), CuspBC hle U :=
  ⟨GlobalTheory.SecFieldChange.secBC_holds hle, fun _ U => GlobalTheory.SecFieldChange.cuspBC_holds hle U⟩

end GlobalTheory.FieldBC
end

