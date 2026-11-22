import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2163
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2154
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2156
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCountableCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open Filter Topology

noncomputable section

namespace GlobalTheory.CountableCharts

theorem isHolTo_finChart_symm {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (c : GlobalTheory.AlgChart p σ D) : IsHolTo c.finChart.target fun z => (c.finChart.symm z).1 := by
  have h1 := GlobalTheory.LocLift.isHolTo_comp (GlobalTheory.TrueCx.TorHolo.isHolTo_symm c) c.finChart.open_target
    (β := fun z => (EuclideanSpace.equiv (Fin D) ℂ).symm z)
    (EuclideanSpace.equiv (Fin D) ℂ).symm.differentiable.differentiableOn fun z hz => hz
  refine GlobalTheory.LocLift.isHolTo_congr h1 fun v _ => ?_
  simp [GlobalTheory.AlgChart.finChart_symm_apply]

theorem exists_countable_charts : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (d : ℕ), SmoothOfRelativeDimension d s → QuasiCompact s → ∀ (Q : Set (Fin d → ℂ) → ((Fin d → ℂ) → (Sp ℂ ⟶ X)) → Prop), (∀ B y b₀, IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap (RingHom.id ℂ)) → IsHolTo B y → ∃ B', IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ Q B' y) → ∃ (K : Type) (_ : Countable K) (B : K → Set (Fin d → ℂ)) (y : K → (Fin d → ℂ) → (Sp ℂ ⟶ X)), (∀ i, IsOpen (B i) ∧ (∀ b ∈ B i, y i b ≫ s = spMap (RingHom.id ℂ)) ∧ IsHolTo (B i) (y i) ∧ Set.InjOn (y i) (B i) ∧ Q (B i) (y i)) ∧ ∀ x : Sp ℂ ⟶ X, x ≫ s = spMap (RingHom.id ℂ) → ∃ i, x ∈ y i '' B i := by
  intro X s d hs hq Q hQ
  haveI := hs
  haveI := hq
  haveI : Smooth s := SmoothOfRelativeDimension.smooth d s
  have hc : ∀ x : GlobalTheory.CxPts s (RingHom.id ℂ), ∃ c : GlobalTheory.AlgChart s (RingHom.id ℂ) d, x ∈ c.e.source :=
    fun x => GlobalTheory.AlgChart.exists_mem_source x
  choose c hc using hc
  have hB : ∀ x : GlobalTheory.CxPts s (RingHom.id ℂ), ∃ B', IsOpen B' ∧ (c x).finChart x ∈ B' ∧
      B' ⊆ (c x).finChart.target ∧ Q B' (fun z => ((c x).finChart.symm z).1) := fun x =>
    hQ _ _ _ (c x).finChart.open_target ((c x).finChart.map_source (hc x))
      (fun b _ => ((c x).finChart.symm b).2) (isHolTo_finChart_symm (c x))
  choose B' hB'o hB'm hB'sub hB'Q using hB
  have hN : ∀ x : GlobalTheory.CxPts s (RingHom.id ℂ),
      (c x).finChart.source ∩ (c x).finChart ⁻¹' B' x ∈ 𝓝 x := fun x =>
    ((c x).finChart.isOpen_inter_preimage (hB'o x)).mem_nhds ⟨hc x, hB'm x⟩
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.countable_cover_nhds hN
  refine ⟨T, hTc.to_subtype, fun i => B' i, fun i z => ((c i).finChart.symm z).1, fun i =>
    ⟨hB'o i, fun b _ => ((c i).finChart.symm b).2,
      GlobalTheory.LocLift.isHolTo_mono (isHolTo_finChart_symm (c i)) (hB'o i) (hB'sub i), ?_, hB'Q i⟩, ?_⟩
  · intro a ha b hb hab
    exact (c i).finChart.symm.injOn (by simpa using hB'sub i ha) (by simpa using hB'sub i hb)
      (Subtype.ext hab)
  · intro x hx
    have hmem : (⟨x, hx⟩ : GlobalTheory.CxPts s (RingHom.id ℂ)) ∈ ⋃ t ∈ T,
        (c t).finChart.source ∩ (c t).finChart ⁻¹' B' t := hTU ▸ Set.mem_univ _
    obtain ⟨t, ht, hm⟩ := Set.mem_iUnion₂.1 hmem
    exact ⟨⟨t, ht⟩, (c t).finChart ⟨x, hx⟩, hm.2, by
      show ((c t).finChart.symm ((c t).finChart ⟨x, hx⟩)).1 = x
      rw [(c t).finChart.left_inv hm.1]⟩

end GlobalTheory.CountableCharts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualWeylTensorLiftCoefficientSpace
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRead.ExPhi

theorem res_eq {ι : Type} {n : ℕ} {lam : ι → DomWeight n} {lamW : ι → ℕ → ℕ} {c : ι → ℤ} (h : Shift lam lamW c) (τ : ι) :
    res n (lamW τ) = fun a => (lam τ).natW a + lamW τ (n - 1) := by
  funext a
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) a.2
  have h1 := h τ a
  have h2 := h τ ⟨n - 1, by omega⟩
  have h3 : (lam τ).w ⟨n - 1, by omega⟩ ≤ (lam τ).w a := (lam τ).anti (by
    rw [Fin.le_def]; have := a.2; simp only; omega)
  simp only [res, DomWeight.natW, DomWeight.detShift, dif_pos hn] at h2 ⊢
  omega

theorem liftPol_mem {K C : Type} [Field K] [Field C] (e0 : K →+* C) {ι : Type} {n : ℕ} {lam : ι → DomWeight n}
    {lamW : ι → ℕ → ℕ} {c : ι → ℤ} (h : Shift lam lamW c) (τ : ι) (x : MvPolynomial (Fin n × Fin n) K)
    (hx : x ∈ nablaSq K n (lam τ)) : liftPol e0 (lamW τ (n - 1)) x ∈ dualWeyl C n n (res n (lamW τ)) := by
  rw [res_eq h τ]
  exact GlobalTheory.T.variableMatrixDetPoly_pow_mul_mem_dualWeyl C n _ _ _ (dualWeylMap K C e0 n n _ x hx)

theorem ssB_span (K : Type) [Field K] {n : ℕ} (ν : Fin n → ℕ) :
    Submodule.span K (Set.range (ssB K ν)) = dualWeyl K n n ν :=
  (Formalism.GradedWeylDivisibility.sSBasis K n n ν).choose_spec.1.2.1

theorem ssB_mem (K : Type) [Field K] {n : ℕ} (l : DomWeight n) (j : ssIdx n n l.natW) : ssB K l.natW j ∈ nablaSq K n l := by
  unfold nablaSq
  rw [← ssB_span]
  exact Submodule.subset_span ⟨j, rfl⟩

theorem detPol_ne_zero (R : Type) [CommRing R] [Nontrivial R] (n : ℕ) : detPol R n ≠ 0 := by
  intro h
  have h1 := congrArg (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2) h
  rw [detPol, RingHom.map_det, map_zero] at h1
  have h2 : (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2).mapMatrix
      (Matrix.of fun a s => X (a, s)) = (1 : Matrix (Fin n) (Fin n) R) := by
    ext a s; simp
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem linInd_map {F K σ ι : Type} [Field F] [Field K] (e : F →+* K) {v : ι → MvPolynomial σ F}
    (hv : LinearIndependent F v) : LinearIndependent K (fun i => MvPolynomial.map e (v i)) := by
  classical
  letI : Algebra F K := e.toAlgebra
  rw [linearIndependent_iff'] at hv ⊢
  intro s c hsum i hi
  let B := Module.Free.chooseBasis F K
  apply B.ext_elem
  intro j
  have key : ∑ i ∈ s, (B.repr (c i) j) • v i = 0 := by
    ext m
    have h1 := congrArg (coeff m) hsum
    simp only [coeff_sum, coeff_smul, coeff_map, smul_eq_mul, coeff_zero] at h1 ⊢
    have h2 := congrArg (fun x => B.repr x j) h1
    simp only [map_sum, map_zero, Finsupp.finset_sum_apply, Finsupp.coe_zero, Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h3 : c i * e (coeff m (v i)) = coeff m (v i) • c i := by
      rw [Algebra.smul_def, mul_comm]; rfl
    rw [h3, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  have := hv s (fun i => B.repr (c i) j) key i hi
  simpa using this

def semiConstr {K C V M I : Type} [Field K] [Field C] [AddCommGroup V] [Module K V] [AddCommGroup M] [Module C M] [Fintype I]
    (e : K →+* C) (b : Module.Basis I K V) (t : I → M) : V →ₛₗ[e] M where
  toFun v := ∑ i, e (b.repr v i) • t i
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a v := by simp [Finset.smul_sum, mul_smul]

theorem semiConstr_basis {K C V M I : Type} [Field K] [Field C] [AddCommGroup V] [Module K V] [AddCommGroup M] [Module C M]
    [Fintype I] (e : K →+* C) (b : Module.Basis I K V) (t : I → M) (i : I) : semiConstr e b t (b i) = t i := by
  classical
  change ∑ j, e (b.repr (b i) j) • t j = t i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Finsupp.single_apply, hj.symm]
  · simp

def mulMap (C : Type) [Field C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) :
    NablaT C n lamW →ₗ[C] Pol C ι n :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra C ι (Pol C ι n)).compLinearMap fun τ =>
    (blockEmb C τ).toLinearMap ∘ₗ (dualWeyl C n n (res n (lamW τ))).subtype)

theorem mulMap_tprod (C : Type) [Field C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ)
    (y : ∀ τ, dualWeyl C n n (res n (lamW τ))) :
    mulMap C n lamW (PiTensorProduct.tprod C y) = ten fun τ => (y τ : MvPolynomial (Fin n × Fin n) C) := by
  simp [mulMap, ten]

theorem ten_liftPol {K C : Type} [Field K] [Field C] (e0 : K →+* C) {ι : Type} [Fintype ι] {n : ℕ} (k : ι → ℕ)
    (x : ι → MvPolynomial (Fin n × Fin n) K) :
    (ten fun τ => liftPol e0 (k τ) (x τ)) = (ten fun τ => detPol C n ^ k τ) * MvPolynomial.map e0 (ten x) := by
  simp only [ten, liftPol, map_mul, map_prod, Finset.prod_mul_distrib, blockEmb, map_rename]

theorem ten_det_ne_zero (C : Type) [Field C] {ι : Type} [Fintype ι] {n : ℕ} (k : ι → ℕ) :
    (ten fun τ => detPol C n ^ k τ) ≠ 0 := by
  unfold ten
  refine Finset.prod_ne_zero_iff.2 fun τ _ => ?_
  intro h
  have hinj : Function.Injective (blockEmb C (k := n) (n := n) τ) :=
    rename_injective _ fun a b hab => (Prod.mk.inj hab).2
  exact pow_ne_zero _ (detPol_ne_zero C n) (hinj (h.trans (map_zero _).symm))

theorem exists_phi (K C : Type) [Field K] [Field C] (e0 : K →+* C) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ)
    (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (h : Shift lam lamW c) :
    ∃ Φ : VV K lam →ₛₗ[e0] NablaT C n lamW, IsPhi e0 lam lamW Φ ∧ LinearIndependent C fun i => Φ (bVV K lam i) := by
  classical
  let u : ∀ τ, ssIdx n n (lam τ).natW → dualWeyl C n n (res n (lamW τ)) := fun τ j =>
    ⟨liftPol e0 (lamW τ (n - 1)) (ssB K (lam τ).natW j), liftPol_mem e0 h τ _ (ssB_mem K _ j)⟩
  let t : VVIdx lam → NablaT C n lamW := fun i => PiTensorProduct.tprod C fun τ => u τ (i τ)
  refine ⟨semiConstr e0 (bVV K lam) t, ?_, ?_⟩
  · intro x v hx hv
    haveI : ∀ τ, Fintype (ssIdx n n (lam τ).natW) := fun τ => (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).fintype
    have hex : ∀ τ, ∃ a : ssIdx n n (lam τ).natW → K, ∑ j, a j • ssB K (lam τ).natW j = x τ := fun τ => by
      have h1 := hx τ
      unfold nablaSq at h1
      rw [← ssB_span] at h1
      exact (Submodule.mem_span_range_iff_exists_fun K).1 h1
    choose a ha using hex
    have hv' : v = ∑ i : VVIdx lam, (∏ τ, a τ (i τ)) • bVV K lam i := by
      apply Subtype.ext
      rw [hv]
      simp only [Submodule.coe_sum, Submodule.coe_smul, bVV_coe, bVVfun, ten, ← ha, map_sum, map_smul]
      rw [Finset.prod_univ_sum]
      simp only [Finset.prod_smul]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext i; simp
    refine ⟨fun τ => ∑ j, e0 (a τ j) • u τ j, fun τ => ?_, ?_⟩
    · simp only [Submodule.coe_sum, Submodule.coe_smul, u, liftPol, ← ha, map_sum, Finset.mul_sum, smul_eq_C_mul, map_mul, map_C]
      refine Finset.sum_congr rfl fun j _ => by ring
    · rw [MultilinearMap.map_sum, hv', map_sum]
      simp only [LinearMap.map_smulₛₗ, semiConstr_basis, MultilinearMap.map_smul_univ, map_prod]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext i; simp
  · simp only [semiConstr_basis]
    refine LinearIndependent.of_comp (mulMap C n lamW) ?_
    have h1 := linInd_map e0 (bVVfun_spec K lam).1
    have h2 := h1.map' (LinearMap.mulLeft C (ten fun τ => detPol C n ^ lamW τ (n - 1)))
      (LinearMap.ker_eq_bot.2 (mul_right_injective₀ (ten_det_ne_zero C _)))
    have h3 : (mulMap C n lamW ∘ t) = (LinearMap.mulLeft C (ten fun τ => detPol C n ^ lamW τ (n - 1))) ∘
        fun i => MvPolynomial.map e0 (bVVfun K lam i) := by
      funext i
      simp only [Function.comp, t, mulMap_tprod, u, ten_liftPol, LinearMap.mulLeft_apply, bVVfun]
    exact h3 ▸ h2

end GlobalTheory.FrameRead.ExPhi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameTangentVectorsOfIsGrpPullback
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist.FrameLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {K : Type} [CommRing K] {x : Sp K ⟶ Xo.X} {A : Over (Sp K)} [GrpObj A]
  {π : A.left ⟶ Xo.univ.t.G.left}

theorem one_comp (hπ : IsGrpPullback A Xo.univ.t.G x π) :
    η[A].left ≫ π = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom hπ (𝟙_ (Over (Sp K)))))
  have e₁ : (1 : 𝟙_ (Over (Sp K)) ⟶ A) = η[A] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  rw [GlobalTheory.ArcQ.NormalForm.one_left_eq, GlobalTheory.ArcQ.NormalForm.one_left_eq]
  simp

theorem exists_lift (hπ : IsGrpPullback A Xo.univ.t.G x π) {T : Over (Sp K)} (v : T.left ⟶ Xo.univ.t.G.left)
    (hv : v ≫ Xo.univ.t.G.hom = T.hom ≫ x) : ∃ w : T ⟶ A, w.left ≫ π = v :=
  ⟨Over.homMk (hπ.1.lift v T.hom hv) (hπ.1.lift_snd _ _ _), hπ.1.lift_fst _ _ _⟩

theorem tan_iff (hπ : IsGrpPullback A Xo.univ.t.G x π) (w : epsR K ⟶ A) : IsTanAt x (w.left ≫ π) ↔ IsTangent w := by
  have hw : w.left ≫ A.hom = spMap (algebraMap K (DualNumber K)) := Over.w w
  constructor
  · intro h
    apply hπ.1.hom_ext
    · rw [Category.assoc]; exact h.2.trans (one_comp hπ).symm
    · have a : η[A].left ≫ A.hom = 𝟙 _ := Over.w η[A]
      rw [Category.assoc, hw, a, ← Geo.Tor.spMap_comp]
      have : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap K (DualNumber K)) = RingHom.id K := by
        ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]
      exact Spec.map_id _
  · intro h
    refine ⟨by rw [Category.assoc, hπ.1.w, ← Category.assoc, hw], ?_⟩
    rw [← Category.assoc]
    exact (congrArg (· ≫ π) h).trans (one_comp hπ)

theorem eig_iff (hπ : IsGrpPullback A Xo.univ.t.G x π) {f : A ⟶ A} {g : Xo.univ.t.G ⟶ Xo.univ.t.G}
    (hf : f.left ≫ π = π ≫ g.left) (w : epsR K ⟶ A) (s : K) :
    (w.left ≫ π) ≫ g.left = spMap (epsMul s) ≫ w.left ≫ π ↔
      w ≫ f = GlobalTheory.GrpTangent.epsScale s ≫ w := by
  have hw : w.left ≫ A.hom = spMap (algebraMap K (DualNumber K)) := Over.w w
  have e : (w.left ≫ π) ≫ g.left = (w ≫ f).left ≫ π := by
    rw [Over.comp_left, Category.assoc, Category.assoc, hf]
  rw [e]
  constructor
  · intro h
    apply Over.OverMorphism.ext
    apply hπ.1.hom_ext
    · simp only [Over.comp_left, GlobalTheory.GrpTangent.epsScale_left, Category.assoc] at h ⊢
      exact h
    · rw [Over.w, Over.w]
  · intro h
    rw [h, Over.comp_left, GlobalTheory.GrpTangent.epsScale_left, Category.assoc]
    rfl

theorem push_prod (hπ : IsGrpPullback A Xo.univ.t.G x π) {n : ℕ} (u : Fin n → (epsR K ⟶ A)) :
    ((List.ofFn u).prod).left ≫ π = ((List.ofFn fun i => pushHom hπ (epsR K) (u i)).prod).left := by
  have := map_list_prod (pushHom hπ (epsR K)) (List.ofFn u)
  rw [List.map_ofFn] at this
  exact congrArg (fun q => q.left) this

theorem isLieComb_of_isCombAt (hπ : IsGrpPullback A Xo.univ.t.G x π) {n : ℕ} (v : Fin n → (epsR K ⟶ A))
    (cf : Fin n → K) (w : epsR K ⟶ A)
    (h : IsCombAt x (fun i => (v i).left ≫ π) cf (w.left ≫ π)) : IsLieComb cf v w := by
  obtain ⟨u, hu, hw⟩ := h
  choose u' hu' using fun i => exists_lift hπ (T := epsR K) (u i).left (Over.w (u i))
  have e : u = fun i => pushHom hπ (epsR K) (u' i) := funext fun i => Over.OverMorphism.ext (hu' i).symm
  refine ⟨u', fun i => ?_, Over.OverMorphism.ext ?_⟩
  · apply hπ.1.hom_ext
    · rw [Category.assoc]; exact (hu' i).trans (hu i)
    · have hv : (v i).left ≫ A.hom = spMap (algebraMap K (DualNumber K)) := Over.w (v i)
      rw [Over.w, Category.assoc, hv, ArcQ.NormalForm.ExFr.scale_over]; rfl
  · apply hπ.1.hom_ext
    · rw [e] at hw
      exact hw.symm.trans (push_prod hπ u').symm
    · rw [Over.w, Over.w]

end GlobalTheory.KSExist.FrameLift

namespace GlobalTheory.KSExist

open FrameLift

theorem exists_frame_of_isGrpPullback {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] (y : FrPt Xo c K)
    {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left} (hπ : IsGrpPullback A Xo.univ.t.G y.x π)
    (a : OAct (𝓞 E) A) (ha : ∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) :
    ∃ ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧
      (∀ σ k, IsTangent (ub σ k)) ∧
      (∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F K (embK c σ z)) ≫ ub σ k) ∧
      ∀ σ (w : epsR K ⟶ A), IsTangent w →
        (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F K (embK c σ z)) ≫ w) →
        ∃ cf, IsLieComb cf (ub σ) w := by
  choose ub hub using fun σ k => exists_lift hπ (T := epsR K) (y.u σ k) (y.tan σ k).1
  refine ⟨ub, hub, fun σ k => (tan_iff hπ _).1 (by rw [hub]; exact y.tan σ k), fun σ k z => ?_, fun σ w ht he => ?_⟩
  · refine (eig_iff hπ (ha z) _ _).1 ?_
    rw [hub]
    exact y.eig σ k z
  · have e : y.u σ = fun i => (ub σ i).left ≫ π := funext fun i => (hub σ i).symm
    obtain ⟨cf, hcf, -⟩ := y.basis σ (w.left ≫ π) ((tan_iff hπ w).2 ht)
      (fun z => (eig_iff hπ (ha z) w _).2 (he z))
    rw [e] at hcf
    exact ⟨cf, isLieComb_of_isCombAt hπ _ cf w hcf⟩

end GlobalTheory.KSExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicQuotientAlongArc
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

section ArcQuot

variable {Y : Scheme.{0}} {W : Y.Opens}

theorem arcPt_mem_basicOpen (hW : IsAffineOpen W) (φ : Γ(Y, W) →+* ℂ) (q : Γ(Y, W)) (s : Sp ℂ) :
    (spMap φ ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) s ∈ Y.basicOpen q ↔ φ q ≠ 0 := by
  change (spMap φ) s ∈ hW.fromSpec ⁻¹ᵁ Y.basicOpen q ↔ _
  rw [hW.fromSpec_preimage_basicOpen q]
  haveI := s.isPrime
  have hs : s.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  change q ∉ (Ideal.comap φ s.asIdeal) ↔ _
  rw [hs]
  simp [Ideal.mem_comap]

theorem evalPt_arcPt (hW : IsAffineOpen W) (φ : Γ(Y, W) →+* ℂ)
    (h : ⊤ ≤ (spMap φ ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ W) :
    GlobalTheory.TangentOrigin.evalPt (spMap φ ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) W h = φ := by
  have := GlobalTheory.TangentOrigin.eq_spec_fromSpec hW _ h
  dsimp only [spMap] at this
  rw [cancel_mono] at this
  have := Spec.map_injective this
  exact (congrArg CommRingCat.Hom.hom this).symm

theorem arcPt_top_le (hW : IsAffineOpen W) (φ : Γ(Y, W) →+* ℂ) :
    ⊤ ≤ (spMap φ ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ W := by
  rw [Scheme.Hom.comp_preimage]
  change ⊤ ≤ spMap φ ⁻¹ᵁ (hW.fromSpec ⁻¹ᵁ W)
  rw [hW.fromSpec_preimage_self]
  exact le_rfl

theorem exists_punctured_ne_zero {f : ℂ → ℂ} {r : ℝ} (hf : DifferentiableOn ℂ f (Metric.ball 0 r))
    {u₀ : ℂ} (hu₀ : u₀ ∈ Metric.ball (0 : ℂ) r) (h₀ : f u₀ ≠ 0) (hr : 0 < r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → f u ≠ 0 := by
  have ha := hf.analyticOnNhd Metric.isOpen_ball
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := Metric.mem_ball_self hr
  rcases (ha 0 h0).eventually_eq_zero_or_eventually_ne_zero with hz | hz
  · exact absurd (ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) r).isPreconnected h0 hz hu₀) h₀
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at hz
    obtain ⟨ε, hε, hz⟩ := hz
    refine ⟨min ε r, lt_min hε hr, min_le_right _ _, fun u hu hu0 => hz u ?_ hu0⟩
    exact Metric.ball_subset_ball (min_le_left _ _) hu

end ArcQuot

end GlobalTheory.Vanishing

namespace GlobalTheory.Vanishing

theorem exists_quot_along_arc : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} (m : H0 p B O) (W : Y.Opens) (hW : IsAffineOpen W) (i : B.ι), W ≤ B.U i → ∀ (ψ : ℂ → (Γ(Y, W) →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ O) → ∃ (ρ : ℝ) (a b : Γ(Y, W)), 0 < ρ ∧ ρ ≤ r ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → ψ u b ≠ 0 ∧ ∀ (hO : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ O) (hi : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ B.U i), H0.val (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) i hO hi m * ψ u b = ψ u a := by
  intro k _ Y p B O m W hW i hWi ψ r hψ hout
  obtain ⟨hr, hhol⟩ := hψ
  have hu₀ : ((r / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hr)]
    linarith
  have hu₀0 : ((r / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (half_pos hr).ne'
  obtain ⟨s⟩ : Nonempty (Sp ℂ) := inferInstance
  have hyO : (spMap (ψ (r / 2 : ℝ)) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) s ∈ O :=
    hout _ hu₀ hu₀0 (show s ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  have hyW : (spMap (ψ (r / 2 : ℝ)) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) s ∈ W :=
    arcPt_top_le hW (ψ (r / 2 : ℝ)) (show s ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  obtain ⟨q, hqle, hqy⟩ := hW.exists_basicOpen_le (V := O ⊓ B.U i) ⟨_, hyO, hWi hyW⟩ hyW
  have hq0 : ψ (r / 2 : ℝ) q ≠ 0 := (arcPt_mem_basicOpen hW _ q s).1 hqy
  haveI := hW.isLocalization_basicOpen q
  obtain ⟨n, a, hna⟩ := IsLocalization.Away.surj q (resG Y hqle (m.loc i))
  obtain ⟨ρ, hρ, hρr, hne⟩ := exists_punctured_ne_zero (hhol q) hu₀ hq0 hr
  refine ⟨ρ, a, q ^ n, hρ, hρr, fun u hu hu0 => ?_⟩
  have hqu : ψ u q ≠ 0 := hne u hu hu0
  refine ⟨by rw [map_pow]; exact pow_ne_zero _ hqu, fun hO hi => ?_⟩
  have hD : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ Y.basicOpen q :=
    fun s _ => (arcPt_mem_basicOpen hW (ψ u) q s).2 hqu
  have hWx := arcPt_top_le hW (ψ u)
  have e := congrArg (GlobalTheory.TangentOrigin.evalPt _ _ hD) hna
  have hres (z : Γ(Y, W)) : GlobalTheory.TangentOrigin.evalPt _ _ hD (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen q) z) = ψ u z := by
    exact (GlobalTheory.TangentOrigin.evalPt_res _ (Y.basicOpen_le q) hWx hD z).trans
      (DFunLike.congr_fun (evalPt_arcPt hW (ψ u) hWx) z)
  rw [map_mul, map_pow, hres, hres] at e
  rw [H0.val_apply, ← GlobalTheory.TangentOrigin.evalPt_res _ hqle _ hD, map_pow, e]

end GlobalTheory.Vanishing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalCharactersLinearBarStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_characters_linear_bar : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∃ (ν₀ β₀ : (Fv F v)ˣ →* ℂˣ) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)),
      (∃ t : E →ₐ[F] Fv F v, ν₀ = chrW X.ν t ∨ ν₀ = (chrW X.ν t)⁻¹) ∧
      GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧ GlobalTheory.SmGL.IsSmoothChar β₀ ∧ GlobalTheory.SmGL.IsUnitaryChar β₀ ∧
      Set.BijOn ι (SB (Fin a × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) : Set _) ∧
      (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ →
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ g' 1 (ι φ)) ∧
      (∀ g' : GL (Fin a) (Fv F v), ∃ g ∈ UAt σ G.V (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ g' 1 (ι φ)) ∧
      (∀ h' : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h' (ι φ)) := by
  first | exact @GlobalTheory.WeilLinA.localOps_eq_omA | exact GlobalTheory.WeilLinA.localOps_eq_omA | (intros; apply GlobalTheory.WeilLinA.localOps_eq_omA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitModulusConstantsEquivariantDictionaryStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitModulus_constants_equivariant_dictionary : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ O.EquivAt (κ i) (u • cc) ∧ SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1 ∧ OneMapRow (T.Q.Xo ((i : ℕ) + 1)) O.c' (Wc D i) (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) O.dict O.mu (xiR D) (wtA (κ i)) (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc D.what₂.embLL.toRatAlgHom.fieldRange (cusp (T.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank) (u • cc) 1 := by
  first | exact @GlobalTheory.AdTh.exists_ccIs_equivAt_serOf_oneMapRow_core | exact GlobalTheory.AdTh.exists_ccIs_equivAt_serOf_oneMapRow_core | (intros; apply GlobalTheory.AdTh.exists_ccIs_equivAt_serOf_oneMapRow_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelAtFittedPointsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_at_fitted_points : GlobalTheory.BigTop.Fun.Bundle → GlobalTheory.BigTop.Fun.SetAt → GlobalTheory.RowClaim.LinK → GlobalTheory.RowClaim.InjK → GlobalTheory.RowClaim.ConstK → GlobalTheory.RowClaim.Formula2K → GlobalTheory.BigTop.Fun.Ker @GlobalTheory.BigTop.Fun.Comparison₂ := by
  first | exact @GlobalTheory.BigTop.Fun.ker_tie | exact GlobalTheory.BigTop.Fun.ker_tie | (intros; apply GlobalTheory.BigTop.Fun.ker_tie <;> assumption)
end

