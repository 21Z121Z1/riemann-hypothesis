import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import ReciprocityTheory.SemistableReduction.Bundle0007
import ReciprocityTheory.SemistableReduction.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussAbsMulSupportFinite
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1309
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfIsoOnAllReductions
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LBReductions

theorem exists_kernel_approx {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) {a b : ℕ}
    (D : Matrix (Fin b) (Fin a) R) : ∃ e : ℕ, ∀ v : Fin a → R, (∀ j, D.mulVec v j ∈ I ^ (e + 1)) →
      ∃ w : Fin a → R, D.mulVec w = 0 ∧ ∀ k, v k - w k ∈ I := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range D.mulVecLin)
  refine ⟨c, fun v hv => ?_⟩
  have h₁ : D.mulVec v ∈ I ^ (c + 1) • (⊤ : Submodule R (Fin b → R)) ⊓ LinearMap.range D.mulVecLin := by
    refine ⟨?_, v, rfl⟩
    rw [pi_eq_sum_univ (D.mulVec v)]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hv j) trivial
  rw [hc (c + 1) (Nat.le_succ c), Nat.add_sub_cancel_left, pow_one] at h₁
  have h₂ : D.mulVec v ∈ Submodule.map D.mulVecLin (I • ⊤) := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact Submodule.smul_mono le_rfl inf_le_right h₁
  obtain ⟨u, hu, huv⟩ := h₂
  have h₃ : ∀ k, u k ∈ I := by
    refine Submodule.smul_induction_on hu (fun r hr n _ k => I.mul_mem_right _ hr)
      fun x y hx hy k => I.add_mem (hx k) (hy k)
  refine ⟨v - u, ?_, fun k => by simpa using h₃ k⟩
  rw [Matrix.mulVec_sub, sub_eq_zero]
  exact huv.symm

open GlobalTheory.AbLaw.Seesaw in

theorem mem_basicOpen_loc₀ {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} {N : LB X} (P : Perf f N) {v w : Fin P.a → R} (h : ∀ k, v k - w k ∈ I)
    {i : P.I} {x : X} (hI : I ≤ (f x).asIdeal) (hx : x ∈ X.basicOpen (loc₀ P v i)) :
    x ∈ X.basicOpen (loc₀ P w i) := by
  have hi : x ∈ P.W i := X.basicOpen_le _ hx
  rw [X.mem_basicOpen _ x hi] at hx ⊢
  by_contra hw
  have e : loc₀ P v i = loc₀ P w i + ∑ k, cst f (P.W i) (v k - w k) * P.u k i := by
    simp only [loc₀, map_sub, sub_mul, Finset.sum_sub_distrib, add_sub_cancel]
  refine (IsLocalRing.notMem_maximalIdeal.2 hx) ?_
  rw [e, map_add, map_sum]
  refine Ideal.add_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hw) (Ideal.sum_mem _ fun k _ => ?_)
  rw [map_mul]
  refine Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_)
  exact (mem_basicOpen_cst f _ _ hi).1 ((X.mem_basicOpen _ x hi).2 hu) (hI (h k))

open GlobalTheory.AbLaw.Seesaw in

theorem triv_of_levels {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R} (hI : I ≤ Ideal.jacobson ⊥)
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} [UniversallyClosed f] {N : LB X} (hN : N.IsLB)
    (P : Perf f N) {Y : ℕ → Scheme.{0}} {b : ∀ e, Y e ⟶ X}
    {q : ∀ e, Y e ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))} (hb : ∀ e, IsPullback (b e) (q e) f (thick R I e))
    (ht : ∀ e, Triv (N.pull (b e))) : Triv N := by
  obtain ⟨e, he⟩ := exists_kernel_approx I P.D₀
  obtain ⟨v', hv', hu, -⟩ := loc_of_triv P (hb e) hN (ht e)
  choose v hv using fun k => Ideal.Quotient.mk_surjective (v' k)
  obtain rfl : Ideal.Quotient.mk (I ^ (e + 1)) ∘ v = v' := funext hv
  obtain ⟨w, hw, hvw⟩ := he v fun j => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_mulVec]
    exact congrFun hv' j
  let G : X.Opens := ⨆ i, X.basicOpen (loc₀ P w i)
  have hZ : IsClosed (f '' (G : Set X)ᶜ) := f.isClosedMap _ G.isOpen.isClosed_compl
  have hG : ∀ x, x ∈ G := by
    intro x
    by_contra hx
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ (f x).isPrime.ne_top
    have hsp : f x ⤳ (⟨m, hm.isPrime⟩ : PrimeSpectrum R) := (PrimeSpectrum.le_iff_specializes _ _).1 hle
    obtain ⟨x', hx', hfx⟩ := hsp.mem_closed hZ ⟨x, hx, rfl⟩
    have hIm : I ≤ m := hI.trans (sInf_le ⟨bot_le, hm⟩)
    have hr : f x' ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (e + 1)))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, hfx]
      exact (Ideal.pow_le_self (Nat.succ_ne_zero e)).trans hIm
    obtain ⟨z, hz⟩ := hr
    obtain ⟨y, rfl, -⟩ := Scheme.exists_preimage_of_isPullback (hb e) x' z hz.symm
    obtain ⟨i, hi⟩ := exists_mem P (b e y)
    have h₁ := hu i
    rw [loc_comp P (hb e)] at h₁
    have h₂ := mem_of_isUnit h₁ (y := y) hi
    rw [← Scheme.preimage_basicOpen] at h₂
    exact hx' (TopologicalSpace.Opens.mem_iSup.2 ⟨i, mem_basicOpen_loc₀ P hvw (by rw [hfx]; exact hIm) h₂⟩)
  have hid : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  refine GlobalTheory.AbTriv.triv_of_pull_id (triv_of_loc P hid (RingHom.id R ∘ w) ?_ fun y => ?_)
  · funext j
    rw [← RingHom.map_mulVec, hw]
    rfl
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hG y)
    refine ⟨i, ?_⟩
    rw [loc_comp P hid, ← Scheme.preimage_basicOpen]
    exact hi

theorem lbIso_of_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), Smooth X.hom → IsProjBy X.hom → GeometricallyConnected X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → ∀ M M' : LB X.left, M.IsLB → M'.IsLB → (∀ e, LBIso (M.pull (b e)) (M'.pull (b e))) → LBIso M M' := by
  intro R _ _ I hI X hs hp _ Y b hb M M' hM hM' w
  have := isProper_of_isProjBy R _ _ hp
  have hN := LB.isLB_div hM' hM
  obtain ⟨P⟩ := nonempty_perf_of_smooth_isProjBy R _ _ hs hp _ hN
  exact triv_of_levels (IsAdicComplete.le_jacobson_bot I) hN P hb fun e =>
    GlobalTheory.AlgTower.triv_chart (GlobalTheory.AlgTower.chartPullDiv M' M _) (w e)

end GlobalTheory.LBReductions
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSystemRelationOfGenericPoint
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open AlgebraicGeometry TopologicalSpace CategoryTheory GlobalTheory.Points GlobalTheory.Twist

set_option autoImplicit false

namespace GlobalTheory.Adelic.GenericRel

theorem eval₂_mul_of_isHomogeneous {σ R A : Type} [CommSemiring R] [CommSemiring A] (φ : R →+* A)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) (c : A) (v : σ → A) :
    eval₂ φ (fun i => c * v i) p = c ^ d * eval₂ φ v p := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have : a.degree = d := by rw [Finsupp.degree_eq_weight_one]; exact hp (mem_support_iff.1 ha)
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← this, Finsupp.degree_apply, mul_left_comm]

variable {F : Type} [Field F] (S : LinSys F)

noncomputable def relFn (c : S.L.ι) {r e : ℕ} (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (m : ℕ)
    (a : Fin m → MvPolynomial (Fin r) F) : Γ(S.Y, S.L.U c) :=
  zfun th c ^ m + ∑ k, eval₂ ((resG S.Y le_top).comp (algebraMap F Γ(S.Y, ⊤)))
    (fun i => (S.comb (u i)).f c) (a k) * zfun th c ^ (k : ℕ)

theorem valR_relFn {K : Type} [Field K] (x : Sp K ⟶ S.Y) (c : S.L.ι) (hx : ptOf x ∈ S.L.U c) {r e : ℕ}
    (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F) :
    valR x (S.L.U c) (relFn S c u th m a) = valR x (S.L.U c) (zfun th c) ^ m + ∑ k, eval₂ (S.baseHom x)
      (fun i => valR x (S.L.U c) ((S.comb (u i)).f c)) (a k) * valR x (S.L.U c) (zfun th c) ^ (k : ℕ) := by
  have h := (le_iff_ptOf_mem x _).2 hx
  have hc : (valMap x _ h).hom.comp ((resG S.Y le_top).comp (algebraMap F Γ(S.Y, ⊤))) = S.baseHom x := by
    ext b
    exact ((valR_eq x _ h _).symm.trans (valR_res x le_top h _)).trans (S.valR_algebraMap x b)
  simp only [relFn, valR_eq x _ h, map_add, map_sum, map_mul, map_pow, eval₂_comp_left, hc]
  rfl

theorem relation_of_generic (F : Type) [Field F] (S : LinSys F) (hY : AlgebraicGeometry.IsIntegral S.Y)
    (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (η : S.Y) (hη : IsGenericPoint η Set.univ)
    (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F) (ha : ∀ k, (a k).IsHomogeneous (e * (m - k)))
    (h0 : S.powVal (resPt η) th ^ m + ∑ k, MvPolynomial.eval₂ (S.baseHom (resPt η))
      (fun i => S.val (resPt η) (S.comb (u i))) (a k) * S.powVal (resPt η) th ^ (k : ℕ) = 0)
    (K : Type) [Field K] [Algebra F K] (x : S.Pt K) :
    S.powVal x.1 th ^ m + ∑ k, aeval (fun i => ∑ j, algebraMap F K (u i j) * S.coords x.1 j) (a k) *
      S.powVal x.1 th ^ (k : ℕ) = 0 := by
  have hxU : ptOf x.1 ∈ S.L.U (S.chartAt (ptOf x.1)) := S.mem_chartAt _
  have hηU : ptOf (resPt η) ∈ S.L.U (S.chartAt (ptOf x.1)) := by
    rw [ptOf_resPt]
    exact (hη.mem_open_set_iff (S.L.U _).isOpen).2 ⟨_, trivial, hxU⟩
  obtain ⟨c0, hc0, hv, hp⟩ := S.exists_frame_change (resPt η) _ hηU
  have hzero : valR (resPt η) _ (relFn S (S.chartAt (ptOf x.1)) u th m a) = 0 := by
    rw [valR_relFn S _ _ hηU, hp (e : ℤ) th]
    simp only [hv, zpow_natCast, eval₂_mul_of_isHomogeneous _ (ha _)]
    calc _ = c0 ^ (e * m) * (S.powVal (resPt η) th ^ m + ∑ k, MvPolynomial.eval₂ (S.baseHom (resPt η))
          (fun i => S.val (resPt η) (S.comb (u i))) (a k) * S.powVal (resPt η) th ^ (k : ℕ)) := by
          rw [mul_add, Finset.mul_sum, mul_pow, ← pow_mul]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_pow, ← pow_mul, show e * m = e * (m - k) + e * k by
            rw [← mul_add, Nat.sub_add_cancel k.2.le], pow_add]
          ring
      _ = 0 := by rw [h0, mul_zero]
  have hb : S.Y.basicOpen (relFn S (S.chartAt (ptOf x.1)) u th m a) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hm : η ∈ S.Y.basicOpen (relFn S (S.chartAt (ptOf x.1)) u th m a) :=
      (hη.mem_open_set_iff (S.Y.basicOpen _).isOpen).2 ⟨y, trivial, hy⟩
    rw [← ptOf_resPt η] at hm
    exact ((valR_ne_zero_iff (resPt η) hηU _).2 hm hzero).elim
  have hf : relFn S (S.chartAt (ptOf x.1)) u th m a = 0 := by
    haveI := hY
    exact (basicOpen_eq_bot_iff _).1 hb
  have key := valR_relFn S x.1 _ hxU u th m a
  rw [hf, valR_zero x.1 _ ((le_iff_ptOf_mem _ _).2 hxU)] at key
  have e2 : ∀ i, valR x.1 _ ((S.comb (u i)).f (S.chartAt (ptOf x.1))) =
      ∑ j, algebraMap F K (u i j) * S.coords x.1 j := fun i =>
    (S.val_comb x.1 (u i)).trans (by rw [LinSys.baseHom_ptOver])
  simp only [e2, LinSys.baseHom_ptOver] at key
  simp only [aeval_def]
  exact key.symm

end GlobalTheory.Adelic.GenericRel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLanglandsGaloisCompatStatement
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_langlands_galois_compat : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (B : ValuationSubring Ω) (h : IsPlaceOver B w)
      (rc : GlobalTheory.LocGL.IrrGL (w.adicCompletion E) → GlobalTheory.WeilDeligne.WD h), GlobalTheory.LocLanglands.IsRec h rc →
    ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (S : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ S →
    ∀ t : ℝ, GlobalTheory.WeilDeligne.wdOf h hl ι r = (rc (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw t →
    ∀ g : G E Ω, IsFrob (F := E) B (normV w) g →
      (r (g ^ (-1 : ℤ))).val.charpoly = (S.map fun z : ℂˣ =>
        Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((-t : ℝ) : ℂ)))).prod := by
  first | exact @GlobalTheory.GeomFrobChar.charpoly_geomFrob | exact GlobalTheory.GeomFrobChar.charpoly_geomFrob | (intros; apply GlobalTheory.GeomFrobChar.charpoly_geomFrob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGaussAbsSupportFinite
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open Polynomial (nthRootsFinset)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSFinPart

theorem log_gaussAbs_support_finite {E : Type} [Field E] [NumberField E] {σ : Type}
    (g : MvPolynomial σ E) :
    (Function.support fun v : FinitePlace E => Real.log (gaussAbs v g)).Finite :=
  ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gaussAbs_support_finite g

theorem finPart_props : ∀ (E : Type) [Field E] [NumberField E] (σ τ : Type),
    (∀ g : MvPolynomial σ E, g ≠ 0 → {v : FinitePlace E | gaussAbs v g ≠ 1}.Finite ∧
      ∀ v : FinitePlace E, 0 < gaussAbs v g) ∧
    (∀ (g : MvPolynomial σ E) (g' : MvPolynomial τ E), g ≠ 0 → g' ≠ 0 →
      (∀ v : FinitePlace E, gaussAbs v g' ≤ gaussAbs v g) → finPart g' ≤ finPart g) ∧
    ∀ (g : MvPolynomial σ E) (m : σ →₀ ℕ), coeff m g ≠ 0 →
      -mean E (fun s => Real.log ‖s (coeff m g)‖) ≤ finPart g := by
  intro E _ _ σ τ
  have hd : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := by
    exact_mod_cast Module.finrank_pos
  refine ⟨fun g hg => ⟨?_, fun v => gauss_abs_pos_of_ne_zero v g hg⟩, ?_, ?_⟩
  · exact ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gaussAbs_mulSupport_finite g hg
  · intro g g' hg hg' hle
    unfold finPart
    refine div_le_div_of_nonneg_right ?_ hd.le
    exact finsum_le_finsum' (log_gaussAbs_support_finite g') (log_gaussAbs_support_finite g)
      (fun v => Real.log_le_log (gauss_abs_pos_of_ne_zero v g' hg') (hle v))
  · intro g m hm
    have hg : g ≠ 0 := by
      rintro rfl; exact hm (by simp)
    set c := coeff m g with hc
    have h1 : ∑ᶠ v : FinitePlace E, Real.log (v c) ≤ ∑ᶠ v : FinitePlace E, Real.log (gaussAbs v g) :=
      finsum_le_finsum'
        ((FinitePlace.hasFiniteMulSupport hm).subset (by
          intro v hv h1; apply hv; simp only at h1 ⊢; rw [h1, Real.log_one]))
        (log_gaussAbs_support_finite g)
        (fun v => Real.log_le_log (FinitePlace.pos_iff.mpr hm) (coeff_le_gauss_abs v g m))
    rw [ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.finsum_log_norm c hm] at h1
    unfold mean finPart
    rw [sum_log_norm_embedding_eq c hm, ← neg_div]
    exact div_le_div_of_nonneg_right h1 hd.le

end GlobalTheory.HSFinPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypeSpaceHolomorphicKModuleKilled
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.LowKType

theorem lowKSub_mem_of_forall {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {lam : Fin n → ℝ} {D : Submodule ℂ H} (Q : Submodule ℂ D)
    (hD : ∀ S : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) S → S ≤ D)
    (hQ : ∀ S : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) S → ∀ y : D, (y : H) ∈ S → y ∈ Q) :
    ∀ y : D, (y : H) ∈ lowKSub ε lam σ → y ∈ Q := by
  have hle : lowKSub ε lam σ ≤ Q.map D.subtype := by
    unfold lowKSub
    refine sSup_le fun S hS x hx => ?_
    exact ⟨⟨x, hD S hS hx⟩, hQ S hS ⟨x, hD S hS hx⟩ hx, rfl⟩
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hle hy
  have : z = y := Subtype.ext hzy
  exact this ▸ hz

end GlobalTheory.LowKType

open GlobalTheory.LowKType in
theorem GlobalTheory.HolDS.lowKSub_kMod : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam → IsDS ε lam σ → IsKMod ε σ D E → lowKSub ε lam σ ≤ D ∧ KStab ε E ((lowKSub ε lam σ).comap D.subtype) ∧ (lowKSub ε lam σ).comap D.subtype ≠ ⊥ ∧ ∀ a b : Fin n, ε a = true → ε b = false → ∀ x ∈ (lowKSub ε lam σ).comap D.subtype, E b a x = 0 := by
  intro n ε H _ _ σ D E lam hHC hch hDS hK
  obtain ⟨hC, _, hU, hI, _, hEx, hmin⟩ := hDS
  have hT := fun μ S hS => GlobalTheory.T.kType_le_kFiniteVectors_finiteDimensional n ε H σ D E hC hU hI hK μ S hS
  have hD : ∀ S : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) S → S ≤ D := fun S hS => (hT _ S hS).1
  have hM : IsMin ε E lam := fun μ x hx0 hx => by
    obtain ⟨T, hT'⟩ := hK.ty μ x hx0 hx
    exact hmin μ T hT'
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold lowKSub
    exact sSup_le fun S hS => hD S hS
  · intro a b hab v hv
    exact lowKSub_mem_of_forall ((lowKSub ε lam σ).comap D.subtype |>.comap (E a b)) hD
      (fun S hS y hy => by
        have h3 := (hT _ S hS).2.2.1 a b hab y hy
        show ((E a b y : D) : H) ∈ lowKSub ε lam σ
        exact (le_sSup hS : S ≤ lowKSub ε lam σ) h3) v hv
  · obtain ⟨S, hS⟩ := hEx
    obtain ⟨v, hv0, hvS, _⟩ := hK.hw _ S hS
    intro hbot
    have hv : v ∈ (lowKSub ε lam σ).comap D.subtype := (le_sSup hS : S ≤ lowKSub ε lam σ) hvS
    rw [hbot] at hv
    exact hv0 ((Submodule.mem_bot ℂ).1 hv)
  · intro a b ha hb x hx
    exact (lowKSub_mem_of_forall (LinearMap.ker (E b a)) hD
      (fun S hS y hy => by
        have h := hT _ S hS
        haveI := h.2.1
        exact GlobalTheory.T.pMinus_annihilates_lowestKType_holomorphicChamber n ε D E lam hK.gl hK.unit hHC.1 hch hM (S.comap D.subtype) h.2.1 h.2.2.1 h.2.2.2
          a b ha hb y hy) x hx : x ∈ LinearMap.ker (E b a))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLine
section
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.HSChoice

namespace GlobalTheory.PencilDisc

def line {F R : Type} [CommRing F] [CommRing R] [Algebra F R] {D N : ℕ} (u : Fin D → Fin N → R) (a b : Fin N → R)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) : Polynomial R :=
  aeval (join (fun i j => Polynomial.C (u i j)) fun j => Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X) f

def disc {F R : Type} [CommRing F] [CommRing R] [Algebra F R] {D N : ℕ} (δ : ℕ) (u : Fin D → Fin N → R) (a b : Fin N → R)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) : R :=
  Polynomial.resultant (line u a b f) (Polynomial.derivative (line u a b f)) δ (δ - 1)

theorem map_line {F R S : Type} [CommRing F] [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] {D N : ℕ}
    (φ : R →ₐ[F] S) (u : Fin D → Fin N → R) (a b : Fin N → R) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    (line u a b f).map (φ : R →+* S) = line (fun i j => φ (u i j)) (fun j => φ (a j)) (fun j => φ (b j)) f := by
  have h : (Polynomial.mapAlgHom φ).comp
      (aeval (join (fun i j => Polynomial.C (u i j)) fun j => Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X)) =
      aeval (join (fun i j => Polynomial.C (φ (u i j))) fun j => Polynomial.C (φ (a j)) + Polynomial.C (φ (b j)) * Polynomial.X) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [join]
    · simp [join]
  exact congrArg (fun g : MvPolynomial (Fin (D + 1) × Fin N) F →ₐ[F] Polynomial S => g f) h

theorem map_disc {F R S : Type} [CommRing F] [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] {D N : ℕ}
    (φ : R →ₐ[F] S) (δ : ℕ) (u : Fin D → Fin N → R) (a b : Fin N → R) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    φ (disc δ u a b f) = disc δ (fun i j => φ (u i j)) (fun j => φ (a j)) (fun j => φ (b j)) f := by
  rw [disc, disc, ← map_line φ, Polynomial.derivative_map, ← AlgHom.coe_toRingHom, ← Polynomial.resultant_map_map]

end GlobalTheory.PencilDisc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixCompletionFirstColumn
section
open Matrix GlobalTheory.TorFin

namespace GlobalTheory

open Module

theorem frame_first_column_first_row :
    ∀ (m : ℕ) (v φ : Fin (m + 1) → ℂ), φ ⬝ᵥ v = 1 → ∃ P P' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ,
      P * P' = 1 ∧ (∀ i, P i 0 = v i) ∧ ∀ j, P' 0 j = φ j := by
  intro m v φ h
  let L : (Fin (m + 1) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => φ ⬝ᵥ x
      map_add' := fun x y => dotProduct_add φ x y
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have hL : ∀ x, L x = φ ⬝ᵥ x := fun x => rfl
  have hsurj : LinearMap.range L = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨c • v, by rw [hL, dotProduct_smul, h]; simp⟩
  have hdim : Module.finrank ℂ (LinearMap.ker L) = m := by
    have := LinearMap.finrank_range_add_finrank_ker L
    rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at this
    omega
  let bN := Module.finBasisOfFinrankEq ℂ (LinearMap.ker L) hdim
  have hli : ∀ (c : ℂ), ∀ x ∈ LinearMap.ker L, c • v + x = 0 → c = 0 := by
    intro c x hx hc
    have := congrArg L hc
    rw [map_add, map_smul, LinearMap.mem_ker.mp hx, hL v, h, map_zero] at this
    simpa using this
  have hsp : ∀ z : Fin (m + 1) → ℂ, ∃ c : ℂ, z + c • v ∈ LinearMap.ker L := by
    intro z
    refine ⟨-(L z), ?_⟩
    rw [LinearMap.mem_ker, map_add, map_smul, hL v, h]
    simp
  let b := Module.Basis.mkFinCons v bN hli hsp
  have hb : ⇑b = Fin.cons v (Subtype.val ∘ bN) := Module.Basis.coe_mkFinCons v bN hli hsp
  let e := Pi.basisFun ℂ (Fin (m + 1))
  have hcoord : b.coord 0 = L := by
    refine b.ext fun i => ?_
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [Basis.coord_apply, Basis.repr_self, hb]
      simp [hL, h]
    · rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
      have hmem : b k.succ ∈ LinearMap.ker L := by
        rw [hb]; simp
      rw [LinearMap.mem_ker.mp hmem]
      simp [Fin.succ_ne_zero]
  refine ⟨e.toMatrix b, b.toMatrix e, Basis.toMatrix_mul_toMatrix_flip e b, ?_, ?_⟩
  · intro i
    rw [Basis.toMatrix_apply, hb]
    simp [e]
  · intro j
    rw [Basis.toMatrix_apply]
    have := congrArg (fun f : (Fin (m + 1) → ℂ) →ₗ[ℂ] ℂ => f (e j)) hcoord
    simp only [Basis.coord_apply] at this
    rw [this, hL]
    simp [e, dotProduct_single]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactParabolicUnipotentEqStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximal_compact_parabolic_unipotent_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E), ((GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) = intMat a b w ∧ ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)).map (GlobalTheory.LeviFubini.sM h w) ≤ (GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviFubini.parB h w) := by
  first | exact @GlobalTheory.LeviFubini.IntPts.intPts | exact GlobalTheory.LeviFubini.IntPts.intPts | (intros; apply GlobalTheory.LeviFubini.IntPts.intPts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartParabolicCentralizerIffBlockDiagonStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_compactPart_parabolicCentralizer_iff_blockDiagonal : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w), (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ (hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w) (p : GlobalTheory.LeviDesc.parP a n w), p ∈ cptPart (twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w)) ↔ ∃ t ∈ cptPart (twCent (MonoidHom.id _) m), blk h w t 0 = (p : GLw n w) := by
  first | exact @GlobalTheory.LeviDesc.CptLevi.mem_compactPart_parabolic_iff | exact GlobalTheory.LeviDesc.CptLevi.mem_compactPart_parabolic_iff | (intros; apply GlobalTheory.LeviDesc.CptLevi.mem_compactPart_parabolic_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartRestrictedProductIffForallStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_compactPart_restrictedProduct_iff_forall : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (T : Subgroup X) (Tv : ∀ v, Subgroup (Y v)), (∀ x, x ∈ T ↔ ∀ v, pf v x ∈ Tv v) → (∀ v, ∀ a ∈ Tv v, ∀ b ∈ Tv v, a * b = b * a) → ∀ x, x ∈ cptPart T ↔ ∀ v, pf v x ∈ cptPart (Tv v) := by
  first | exact @GlobalTheory.CptPartRestr.mem_cptPart_iff_forall | exact GlobalTheory.CptPartRestr.mem_cptPart_iff_forall | (intros; apply GlobalTheory.CptPartRestr.mem_cptPart_iff_forall <;> assumption)
end

