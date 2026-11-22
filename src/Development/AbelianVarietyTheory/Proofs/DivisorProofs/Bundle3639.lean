import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3265
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3575
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3636
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3500
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2626
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3586
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparatesOnSmoothOfPair
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3408
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3456
import Development.AbelianVarietyTheory.Definitions.Divisors.TowerRedToBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3290
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyAbelianVarietyCharZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.DeRhamCharpolyZero

open GlobalTheory.AV

theorem charpoly_of_bijective {R K M V : Type*} [CommRing R] [Field K] [Algebra R K] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (E : K ⊗[R] M →ₗ[K] V) (hE : Function.Bijective E) (φ : Module.End R M) (T : Module.End K V)
    (h : ∀ m, T (E (1 ⊗ₜ m)) = E (1 ⊗ₜ φ m)) : T.charpoly = φ.charpoly.map (algebraMap R K) := by
  let e := LinearEquiv.ofBijective E hE
  have hT : T = e.conj (φ.baseChange K) := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨z, rfl⟩ := e.surjective v
    rw [LinearEquiv.conj_apply_apply, e.symm_apply_apply]
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x m =>
      have : x ⊗ₜ[R] m = x • ((1 : K) ⊗ₜ[R] m) := by simp [TensorProduct.smul_tmul']
      rw [this, map_smul, map_smul, map_smul, map_smul]
      exact congrArg (x • ·) (h m)
  rw [hT, LinearEquiv.charpoly_conj, LinearMap.charpoly_baseChange]

theorem charpoly_dualMap {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module.Finite K (Module.Dual K V)] (f : Module.End K V) : (f.dualMap).charpoly = f.charpoly := by
  classical
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis K V),
    ← LinearMap.charpoly_toMatrix f.dualMap (Module.finBasis K V).dualBasis, ← Matrix.charpoly_transpose,
    LinearMap.dualMap_def, LinearMap.toMatrix_transpose, Matrix.transpose_transpose]

theorem finite_prim {K : Type} [Field K] (B : AbVar K) : Module.Finite K (primDR B.X) :=
  (GlobalTheory.abelianDeRham.1.prim B.ab B.smooth).1

theorem finite_HdR {K : Type} [Field K] (B : AbVar K) : Module.Finite K (HdR B.X) :=
  haveI := finite_prim B
  inferInstance

theorem charpoly_push_of_pullback {K L : Type} [Field K] [Field L] [Algebra K L] (B₀ : AbVar K) (B : AbVar L)
    {φ : B.X.left ⟶ B₀.X.left} (h : IsGrpPullback B.X B₀.X (spMap (algebraMap K L)) φ) (f₀ : B₀ ⟶ B₀) (f : B ⟶ B)
    (e : φ ≫ f₀.hom.left = f.hom.left ≫ φ) [Module.Finite K (HdR B₀.X)] [Module.Finite L (HdR B.X)] :
    LinearMap.charpoly (push (dp0 L) (𝟙 _) f.hom) =
      (LinearMap.charpoly (push (dp0 K) (𝟙 _) f₀.hom)).map (algebraMap K L) := by
  haveI := finite_prim B₀
  haveI := finite_prim B
  have m := GlobalTheory.Published.AbelianDeRham.bcMor h
  have hm : m.IsBC := (GlobalTheory.abelianDeRham.2.2.1 K B₀.X B₀.dim B₀.ab B₀.smooth L B.X φ h).1
  have h1 : LinearMap.charpoly (push (dp0 L) (𝟙 _) f.hom) = (primPull (dp0 L) (𝟙 _) f.hom).charpoly :=
    charpoly_dualMap _
  have h2 : LinearMap.charpoly (push (dp0 K) (𝟙 _) f₀.hom) = (primPull (dp0 K) (𝟙 _) f₀.hom).charpoly :=
    charpoly_dualMap _
  rw [h1, h2]
  refine charpoly_of_bijective (liftSemi m.pull) hm _ _ fun c => ?_
  rw [liftSemi_tmul, liftSemi_tmul, one_smul, one_smul]
  have k := (homMor (dp0 K) (𝟙 _) f₀.hom).comp m
  exact (GrpMor.pull_pull m (homMor (dp0 L) (𝟙 _) f.hom) k (fun _ ↦ rfl) e.symm c).trans
    (GrpMor.pull_pull (homMor (dp0 K) (𝟙 _) f₀.hom) m k (fun _ ↦ rfl) rfl c).symm

theorem exists_isGrpPullback_baseChange {K : Type} (L : Type) [Field K] [Field L] [Algebra K L] {B₀ : AbVar K}
    (f₀ : B₀ ⟶ B₀) : ∃ q : (AbVar.baseChange L B₀).X.left ⟶ B₀.X.left,
      IsGrpPullback (AbVar.baseChange L B₀).X B₀.X (spMap (algebraMap K L)) q ∧
      q ≫ f₀.hom.left = (AbVar.bcMap L f₀).hom.left ≫ q :=
  ⟨pullback.fst B₀.X.hom (spMap (algebraMap K L)), isGrpPullback_pullback B₀.X _, (pullback.lift_fst _ _ _).symm⟩

theorem charpoly_of_pullback {K L : Type} [Field K] [Field L] [Algebra K L] (B₀ : AbVar K) (B : AbVar L)
    {φ : B.X.left ⟶ B₀.X.left} (h : IsGrpPullback B.X B₀.X (spMap (algebraMap K L)) φ) (f₀ : B₀ ⟶ B₀) (f : B ⟶ B)
    (e : φ ≫ f₀.hom.left = f.hom.left ≫ φ) : AbVar.charpoly f = AbVar.charpoly f₀ := by
  obtain ⟨q, h', hq⟩ := exists_isGrpPullback_baseChange L f₀
  obtain ⟨i, hi, hφ⟩ := grpPullback_iso h h'
  let u : B ⟶ AbVar.baseChange L B₀ := AbVar.Hom.mk i.hom
  have hu : AbVar.IsIsogeny u := by
    have : IsIso i.hom.left := ⟨⟨i.inv.left, by rw [← Over.comp_left, i.hom_inv_id, Over.id_left],
      by rw [← Over.comp_left, i.inv_hom_id, Over.id_left]⟩⟩
    exact ⟨inferInstanceAs (IsFinite i.hom.left), inferInstanceAs (Surjective i.hom.left)⟩
  rw [← AbVar.charpoly_bcMap K L B₀ f₀]
  refine AbVar.charpoly_eq_of_isogeny_intertwines L B _ u f _ hu (AbVar.hom_ext ?_)
  change f.hom ≫ i.hom = i.hom ≫ (AbVar.bcMap L f₀).hom
  apply Over.OverMorphism.ext
  apply h'.1.hom_ext
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hφ, ← e, ← hq, ← Category.assoc, hφ]
  · rw [Over.w, Over.w]

theorem charpoly_push_complex (B : AbVar ℂ) (f : B ⟶ B) [Module.Finite ℂ (HdR B.X)] :
    LinearMap.charpoly (push (dp0 ℂ) (𝟙 _) f.hom) = (AbVar.charpoly f).map (Int.castRingHom ℂ) := by
  obtain ⟨L, hL, ⟨u⟩⟩ : ∃ L : LB B.X.left, L.IsLB ∧ Nonempty (HolUnif B.X L B.dim) := by
    have := B.ab.proper
    obtain ⟨H, m, s, hH, hs, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple ℂ B.X B.ab
    have hamp : Out.RelAmple B.X H :=
      (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine B.X hH).2 (GlobalTheory.isAmpleLB_of_veryAmpleBy hs)
    exact ⟨_, Out.Inh.trivLB_isLB _, GlobalTheory.RealMultChart.exists_holUnif_of_compact B.X B.dim B.smooth
      (GlobalTheory.RealMultChart.compactSpace_points B.X H hamp)
      (fun a n hn => GlobalTheory.RealMultChart.exists_pow_eq B.X B.ab a n hn)⟩
  have ht := GlobalTheory.TorusTransfer.tangent_bijective u B.smooth
  obtain ⟨M, hM, hΛ, -, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom B.X B.X B.ab B.ab L L B.dim B.dim u u
    ht.1 ht.2 f.hom inferInstance
  obtain ⟨ε, hP⟩ := GlobalTheory.PeriodFamily.periodComparison_holds
  obtain ⟨P, hsp, hrk, -, hnat, -⟩ := hP B.X B.dim B.ab B.smooth L hL u
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  have hr : Module.finrank ℤ u.Λ = 2 * B.dim := by
    rw [ZLattice.rank ℝ u.Λ, Module.finrank_pi_fintype]
    simp [mul_comm]
  let φ : u.Λ →ₗ[ℤ] u.Λ := (M.restrictScalars ℤ).restrict hΛ
  let E : ℂ ⊗[ℤ] u.Λ →ₗ[ℂ] HdR B.X := P.toIntLinearMap.liftBaseChange ℂ
  have hE1 : ∀ x, E (1 ⊗ₜ x) = P x := fun x => one_smul ℂ (P x)
  have hs : Function.Surjective E := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, hE1 x⟩
  have hE : Function.Bijective E :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_baseChange, hr, hrk])).2 hs, hs⟩
  have h1 := charpoly_of_bijective E hE φ (push (dp0 ℂ) (𝟙 _) f.hom) fun x => by
    rw [hE1, hE1]
    exact hnat f.hom M hM x (φ x) rfl
  have hpow : ∀ (n : ℕ) (z : Fin B.dim → ℂ), u.ex (n • z) = u.ex z ^ n := fun n z => by
    induction n with
    | zero => rw [zero_smul, pow_zero]; exact (u.ker 0).2 (zero_mem _)
    | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]
  have hc : ∀ (j : ℕ) (z : Fin B.dim → ℂ), (2 ^ j : ℕ) • (((2 : ℂ) ^ j)⁻¹ • z) = z := fun j z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    simp
  have hc' : ∀ (j : ℕ) (z : Fin B.dim → ℂ), ((2 : ℂ) ^ j)⁻¹ • ((2 ^ j : ℕ) • z) = z := fun j z => by
    rw [smul_comm, hc]
  have h2 := AbVar.charpoly_eq_lattice_model ℂ B f u.Λ φ 2 Nat.prime_two (by norm_num)
    (fun j x => u.ex (((2 : ℂ) ^ j)⁻¹ • (x : Fin B.dim → ℂ)))
    (fun j x y => by
      simp only [Submodule.coe_add, smul_add]
      exact u.ex_add _ _)
    (fun j x => by
      refine Eq.trans ?_ (hM _)
      rw [map_smul]
      rfl)
    (fun j x => by
      refine (u.ker _).trans ⟨fun h => ⟨⟨_, h⟩, Subtype.ext (hc j x).symm⟩, ?_⟩
      rintro ⟨y, rfl⟩
      rw [show ((2 ^ j • y : u.Λ) : Fin B.dim → ℂ) = (2 ^ j : ℕ) • (y : Fin B.dim → ℂ) from rfl, hc']
      exact y.2)
    (fun j q => by
      obtain ⟨z, rfl⟩ := u.ex_onto q
      constructor
      · intro h
        exact ⟨⟨_, (u.ker _).1 ((hpow _ z).trans h)⟩, congrArg u.ex (hc' j z)⟩
      · rintro ⟨x, hx⟩
        have hx' : u.ex (((2 : ℂ) ^ j)⁻¹ • (x : Fin B.dim → ℂ)) = u.ex z := hx
        change u.ex z ^ (2 ^ j) = 1
        rw [← hx', ← hpow, hc]
        exact (u.ker _).2 x.2)
  rw [h1, h2]
  rfl

theorem exists_countable_model (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (B : AbVar k) (f : B ⟶ B) :
    ∃ (K : Type) (_ : Field K) (_ : Countable K) (_ : Algebra K k) (B₀ : AbVar K) (f₀ : B₀ ⟶ B₀)
      (φ : B.X.left ⟶ B₀.X.left), IsGrpPullback B.X B₀.X (spMap (algebraMap K k)) φ ∧
      φ ≫ f₀.hom.left = f.hom.left ≫ φ := by
  obtain ⟨S, A, _, ψ, -, hS, hA, hg, hψ⟩ :=
    GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring k B.dim B.X ∅ B.ab B.smooth
  have hSc : Countable S := by
    obtain ⟨n, p, hp⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hS
    have hc : Countable (MvPolynomial (Fin n) ℤ) := by
      rw [← Cardinal.mk_le_aleph0_iff]
      refine (MvPolynomial.cardinalMk_le_max).trans ?_
      simp
    exact hp.countable
  let F : Subfield k := Subfield.closure (S : Set k)
  have hF : Cardinal.mk F ≤ Cardinal.aleph0 :=
    (Subfield.cardinalMk_closure_le_max _).trans (max_le (Cardinal.mk_le_aleph0_iff.2 hSc) le_rfl)
  let K : IntermediateField F k := algebraicClosure F k
  haveI : IsAlgClosed K := (algebraicClosure.isAlgClosure F k).isAlgClosed
  have hK : Countable K := Cardinal.mk_le_aleph0_iff.1
    ((Algebra.IsAlgebraic.cardinalMk_le_max F K).trans (max_le hF le_rfl))
  let j : S →+* K := S.subtype.codRestrict K fun x => K.algebraMap_mem (⟨x, Subfield.subset_closure x.2⟩ : F)
  have e : spMap (algebraMap K k) ≫ spMap j = spMap S.subtype := by
    rw [← Cris.spMap_comp]
    rfl
  let B₀ : AbVar K :=
    { X := (Over.pullback (spMap j)).obj A
      ab := GlobalTheory.isAbelianScheme_pullback_obj _ A hA
      dim := B.dim
      smooth := (smoothOfRelativeDimension_isStableUnderBaseChange (n := B.dim)).of_isPullback
        (IsPullback.of_hasPullback A.hom (spMap j)) hg }
  obtain ⟨φ, hφ⟩ : ∃ φ : B.X.left ⟶ B₀.X.left, IsGrpPullback B.X B₀.X (spMap (algebraMap K k)) φ :=
    ⟨_, Chart.isGrpPullback_factor (spMap j) (spMap (algebraMap K k)) (hψ.congr e.symm rfl)⟩
  obtain ⟨f₀, hf₀, he⟩ := GlobalTheory.AlgClosedHomDescent.hom_descends K k (algebraMap K k) B₀.X B₀.X B.X B.X φ φ
    B₀.ab B₀.ab hφ hφ f.hom inferInstance
  exact ⟨K, inferInstance, hK, inferInstance, B₀, AbVar.Hom.mk f₀, φ, hφ, he⟩

theorem charpoly_push : ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B) [Module.Finite k (HdR B.X)],
    LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom) = (GlobalTheory.AV.AbVar.charpoly f).map (Int.castRingHom k) := by
  intro k _ _ _ B f _
  obtain ⟨K, _, _, _, B₀, f₀, φ, hφ, he⟩ := exists_countable_model k B f
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap K k).injective).2 inferInstance
  obtain ⟨σ⟩ := GlobalTheory.KeyRuleUnique.nonempty_ringHom_complex K
  letI : Algebra K ℂ := σ.toAlgebra
  haveI := finite_HdR B₀
  haveI := finite_HdR (AbVar.baseChange ℂ B₀)
  obtain ⟨q, hq, hq'⟩ := exists_isGrpPullback_baseChange ℂ f₀
  have h3 := charpoly_push_of_pullback B₀ _ hq f₀ _ hq'
  have h4 := charpoly_push_complex (AbVar.baseChange ℂ B₀) (AbVar.bcMap ℂ f₀)
  rw [AbVar.charpoly_bcMap] at h4
  have h5 : LinearMap.charpoly (push (dp0 K) (𝟙 _) f₀.hom) = (AbVar.charpoly f₀).map (Int.castRingHom K) := by
    apply Polynomial.map_injective (algebraMap K ℂ) σ.injective
    rw [← h3, h4, Polynomial.map_map]
    exact congrArg (Polynomial.map · _) (RingHom.ext_int _ _)
  rw [charpoly_push_of_pullback B₀ B hφ f₀ f he, h5, charpoly_of_pullback B₀ B hφ f₀ f he, Polynomial.map_map]
  exact congrArg (Polynomial.map · _) (RingHom.ext_int _ _)

end GlobalTheory.DeRhamCharpolyZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierTermSystemRegularTraitsGivenChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Poinc.Sep.exists_chartMember_traitsR : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Φ : VSys (id : ℤ → ℤ) g W ((l ^ j) ^ 2) (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m), j₀ ≤ j ∧ HasTraitsR X₁ z₁ Φ.pre ∧ IsChartMember X₁ z₁ Φ Q ξ t δ y ρ e h := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hW hth V _ _ _ Q m t δ hrk ht hsym hnn hpos hmon ξ hξ l hl hln j₀
  obtain ⟨j, X₁, z₁, hdom, Φ, y, ρ, e, h, c₀, hj, hR, hC, hU, hM, hE, hCS⟩ :=
    GlobalTheory.T.exists_fourierTermSystem_traits_chart_thetaModel g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hth V Q m t δ hrk ht hsym hnn hpos hmon ξ hξ l hl hln
      (max j₀ 1)
  obtain ⟨-, -, hIC, -⟩ := GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing g n F W Z i X₁ z₁
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hN : 3 ≤ (l ^ j) ^ 2 := by
    have h2 : 2 ≤ l ^ j := le_trans hl.two_le (Nat.le_self_pow (by omega) l)
    nlinarith
  have hLam : Φ.abelian₂ := GlobalTheory.T.fourierTermSystem_lam_of_exact_class_sums ℤ id g 8 W _ Φ ((l ^ j) ^ 2) (by norm_num) hN hE
  have hFour : Φ.Four ((l ^ j) ^ 2) := GlobalTheory.T.fourierTermSystem_four_of_galois_class_sums ℤ id g 8 W _ Φ ((l ^ j) ^ 2) hCS
  let v : ∀ y', (Φ.V y')ˣ := fun y' => (hU y').unit⁻¹
  have happ : ∀ e' : ℕ, ∃ a : X₁.M.Z.presheaf.stalk z₁, ∀ y', Φ.ev y' a - ((v y')⁻¹ : (Φ.V y')ˣ) ∈
      (maximalIdeal (X₁.M.Z.presheaf.stalk z₁) ^ e').map (Φ.ev y') := by
    intro e'
    obtain ⟨a, ha⟩ := GlobalTheory.T.fourierTermSystem_indexZero_coefficient_approx ℤ id g 8 W _ Φ ((l ^ j) ^ 2) hN hE hLam hFour
      (fun y₁ y₂ h₁ h₂ => (hM y₁ h₁).trans (hM y₂ h₂).symm) c₀ e'
    refine ⟨a, fun y' => ?_⟩
    simpa [v] using ha y'
  have hFour' : (Φ.rescale v).Four ((l ^ j) ^ 2) := GlobalTheory.T.fourierTermSystem_four_rescale_approximated_units ℤ id g 8 W _ Φ ((l ^ j) ^ 2) hFour v happ
  have hLam' : (Φ.rescale v).abelian₂ := hLam
  refine ⟨j, X₁, z₁, (Φ.rescale v).toVSys ((l ^ j) ^ 2) hLam' hFour', y, ρ, e, h,
    le_trans (le_max_left _ _) hj, hR, ?_⟩
  obtain ⟨h1, h2, h3, h4, D, e₈, hS, hT⟩ := hC
  refine ⟨h1, h2, h3, h4, D, e₈, hS, ?_⟩
  have h0 : Φ.term y (fun a => e.symm ((0 : Fin 8 → Q.X) a)) c₀ * ((v y : (Φ.V y)ˣ) : Φ.V y) = 1 := by
    have hz : (fun a => e.symm ((0 : Fin 8 → Q.X) a)) = 0 := by
      funext a; simp
    rw [hz]
    simp [VPre.term, mono, qW, v]
  have := GlobalTheory.T.isThetaTerms_of_mul_index_zero_term_eq_one (Φ.V y) D ((l ^ j) ^ 2) (Fin 8 → Q.X) Φ.Q e₈
    (fun mu c => Φ.term y (fun a => e.symm (mu a)) c) (v y) c₀ hT h0
  refine cast (congrArg (fun T : (Fin 8 → Q.X) → Φ.Q → Φ.V y => IsThetaTerms D ((l ^ j) ^ 2) e₈ T) ?_) this
  funext mu c
  show Φ.u y (fun a => e.symm (mu a)) c * mono W (Φ.t y) (Φ.δ y) (fun a => e.symm (mu a)) * ((v y : (Φ.V y)ˣ) : Φ.V y) =
    Φ.u y (fun a => e.symm (mu a)) c * ((v y : (Φ.V y)ˣ) : Φ.V y) * mono W (Φ.t y) (Φ.δ y) (fun a => e.symm (mu a))
  exact mul_right_comm _ _ _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHeatOperatorsAbelianLocus
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatV
open GlobalTheory.KS

theorem cst_resV {R : Type} [CommRing R] {Y : Scheme.{0}} (π : Y ⟶ Sp R) (c : R) {O : Y.Opens}
    (h : O ≤ π ⁻¹ᵁ (bo R c).1) (a : R) : cst π (bo R c).1 h (resV R c a) = constFn π O a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.map_appLE π h (homOfLE ((Sp R).basicOpen_le (U := ⊤)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c))).op)

theorem field_cst_eq_zero {R : Type} [CommRing R] {Y : Scheme.{0}} (π : Y ⟶ Sp R) (c : R) (dd : Fld Y)
    (hd : IsField ⊤ dd) (h0 : ∀ O a, dd O (constFn π O a) = 0) (O : Y.Opens) (h : O ≤ π ⁻¹ᵁ (bo R c).1)
    (r : Γ(Sp R, (bo R c).1)) : dd O (cst π (bo R c).1 h r) = 0 := by
  let s : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c
  have hu : IsUnit (resV R c c) := IsLocalization.Away.algebraMap_isUnit (S := Γ(Sp R, (Sp R).basicOpen s)) s
  obtain ⟨k, y, hy⟩ := IsLocalization.Away.surj (S := Γ(Sp R, (Sp R).basicOpen s)) s r
  have hy' : r * resV R c (c ^ k) = resV R c ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y) := by
    rw [map_pow]
    refine hy.trans ?_
    show _ = algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y))
    simp
  have e := congrArg (fun z => dd O (cst π (bo R c).1 h z)) hy'
  simp only [map_mul] at e
  have hu' : IsUnit (cst π (bo R c).1 h (resV R c (c ^ k))) := by
    rw [map_pow]
    exact (hu.pow k).map _
  rw [hd.2.1 O le_top, cst_resV π c h (c ^ k), cst_resV, h0, h0, ← cst_resV π c h (c ^ k)] at e
  exact hu'.mul_right_eq_zero.1 (by linear_combination e)

theorem exists_heat_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (c : R), c = ∏ i, tt i → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (DV : Derivation ℤ Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), (∀ r, DV (GlobalTheory.HeatV.resV R c r) = GlobalTheory.HeatV.resV R c (D r)) → IsKS t (GlobalTheory.HeatV.bo R c).1 (GlobalTheory.HeatV.bo R c) (fun a => spMap (dualMap (GlobalTheory.HeatV.resV R c)) ≫ (tv (v' a)).left) ⇑DV Θ₁ → ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → Fld t.G.left) (u : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (pf pf' : ∀ i, Γ(t.G.left, W i)) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧ (∀ i O (h : O ≤ W i) (a : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), d i O (GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) a) = GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) (DV a)) ∧ (∀ (k : ℕ) i i' O (h : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)), GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k O (h.trans (inf_le_left.trans (hW i))) (pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * f) = pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i') (pf i') (pf' i') k O (h.trans (inf_le_right.trans (hW i'))) f) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ htt hab c hc n v' D dd' hdd Θ₁ DV _ hKS
  obtain ⟨J, W, j, d, hW, hcov, hWj, hfld, hlift, hdiff⟩ :=
    ksRel_operators E H R t P m tt htt hab c hc n v' dd' hdd DV Θ₁ hKS
  have hsym := isKS_symm_abLocus E H R t P m tt htt hab c hc n v' dd' hdd DV Θ₁ hKS
  have hkill : ∀ a O (h : O ≤ t.G.hom ⁻¹ᵁ (bo R c).1) (r : Γ(Sp R, (bo R c).1)),
      dd' a O (cst t.G.hom (bo R c).1 h r) = 0 := fun a O h r =>
    field_cst_eq_zero t.G.hom c (dd' a) (hdd a).1
      (fun O' b => GlobalTheory.Heat.Adjust.inv_constFn t.G (v' a) (dd' a) (hdd a) O' b) O h r
  have h2 : IsUnit (2 : Γ(Sp R, (bo R c).1)) := by
    have : IsUnit ((2 : ℚ)) := by norm_num
    have h' := (this.map (algebraMap ℚ R)).map (resV R c)
    rwa [map_ofNat, map_ofNat] at h'
  obtain ⟨e, u, pf, pf', hglue⟩ := GlobalTheory.HeatVAlg.exists_heatV t.G.left (Sp R) t.G.hom (bo R c).1 t.PP.L t.PP.isLB h2 n
    dd' (fun a => (hdd a).1) hkill Θ₁ hsym J W j d hW hWj hfld hdiff
    (GlobalTheory.CechH1Local.exists_dlog_add_coboundary_abLocus E H R t P m tt htt hab c hc n v' dd' hdd J W j hW hcov hWj)
  refine ⟨J, W, j, fun i O' f' => d i O' f' + ∑ a, pbT t.G.hom (e a) O' * dd' a O' f', u, pf, pf', hW, hcov, hWj,
    fun i => ?_, fun i O h a => ?_, hglue⟩
  · have hF := GlobalTheory.Heat.Adjust.isField_add_comb (d i) dd' (fun a => pbT t.G.hom (e a) (W i)) (hfld i)
      fun a => (hdd a).1
    have r : ∀ O, O ≤ W i → ∀ a, rsT (pbT t.G.hom (e a) (W i)) O = pbT t.G.hom (e a) O :=
      fun O h a => rsT_pbT t.G.hom (hW i) h _
    refine ⟨fun O h f f' => ?_, fun O h f f' => ?_, fun O O' hh h f => ?_⟩
    · simpa only [r O h] using hF.1 O h f f'
    · simpa only [r O h] using hF.2.1 O h f f'
    · simpa only [r O h, r O' (hh.trans h)] using hF.2.2 O O' hh h f
  · simp only [hlift i O h a, hkill, mul_zero, Finset.sum_const_zero, add_zero]

end GlobalTheory.HeatV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupTower
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB mulN)
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.SerreTate
open GlobalTheory.DeRham (spOver)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbelianTower

open TensorProduct
open scoped CategoryTheory.Obj

theorem exists_isUnivTorsion {O : Type} [CommRing O] {A : Over (Sp O)} [GrpObj A] (hA : IsAbelianScheme A) {g : ℕ}
    (hg : SmoothOfRelativeDimension g A.hom) {N : ℕ} (hN : N ≠ 0) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (y : SpAlg O R ⟶ A), Module.Finite O R ∧
      Module.Projective O R ∧ AbelianPDiv.IsUnivTorsion N y ∧
      ∀ q : PrimeSpectrum O, Module.rankAtStalk R q = N ^ (2 * g) := by
  obtain ⟨R, _, _, y, h1, h2, h⟩ := AbelianPDiv.exists_isPullback (N := N) hA (Nat.one_le_iff_ne_zero.2 hN)
  refine ⟨R, inferInstance, inferInstance, y, h1, h2, AbelianPDiv.isUnivTorsion_of_isPullback y h, fun q => ?_⟩
  let K := q.asIdeal.ResidueField
  obtain ⟨y', h'⟩ := AbelianPDiv.exists_isPullback_baseChange y h K
  let B : AV.AbVar K :=
    { X := (Over.pullback (spMap (algebraMap O K))).obj A
      ab := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback _ A hA
      dim := g
      smooth := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback A.hom (spMap (algebraMap O K))) hg }
  have hr := AVTower.finrank_torsion B hN (S := K ⊗[O] R) y' h'
  have hq : PrimeSpectrum.comap (algebraMap O K) ⊥ = q :=
    PrimeSpectrum.ext ((RingHom.ker_eq_comap_bot _).symm.trans (Ideal.ker_algebraMap_residueField _))
  rw [← hq, ← Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_finrank_of_free, hr]
  rfl

theorem exists_pDivGroup (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A]
    (hA : IsAbelianScheme A) (g : ℕ) (hg : SmoothOfRelativeDimension g A.hom) :
    ∃ (G : PDivGroup p O) (_ : G.TorsionTower A), G.height = 2 * g := by
  have := hA.comm
  choose R _ _ y h1 h2 h hr using fun n : ℕ => exists_isUnivTorsion (N := p ^ n) hA hg
    (pow_ne_zero _ hp.out.ne_zero)
  choose r r1 r2 r3 using fun n : ℕ => (h n).exists_res (h (n + 1))
    (by rw [pow_succ, pow_mul, (h n).1, one_pow])
  let G : PDivGroup p O :=
    { height := 2 * g
      A := R
      hopf := fun n => (h n).hopfAlgebra
      cocomm := fun n => (h n).isCocomm
      finite := h1
      projective := h2
      rank_eq := fun n q => (hr n q).trans (pow_mul _ _ _).symm
      res := r
      res_surjective := r1
      ker_res := r2 }
  exact ⟨G, {
    y := y
    mul := fun n B _ _ => (h n).mul_y
    inj := fun n B _ _ _ _ => (h n).inj
    surj := fun n B _ _ z hz => ((h n).2 B z hz).exists
    res := r3 }, rfl⟩

theorem exists_pDivGroup_tower : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (G : PDivGroup p R) (_ : G.TorsionTower A), G.height = 2 * g :=
  fun p _ R _ _ A _ g hA hg => exists_pDivGroup p R A hA g hg

end GlobalTheory.AbelianTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsDeRhamPairing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UPel.HT.CorrForm
open GlobalTheory.AbDual

theorem exists_isCorrForm_obj : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ := by
  intro p _ D R _ b N _ _ k _ _ t o₀
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o₀.A o₀.ab
  have C := cupSquare_of_free GlobalTheory.abelianDeRham.1 (AbelianSchemeGerms.isAbelianScheme_tensor o₀.A o₀.A o₀.ab o₀.ab)
    (smooth_prod hg hg)
  exact exists_isCorrForm C o₀.isLB o₀.rig₁ o₀.rig₂

end GlobalTheory.UPel.HT.CorrForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackBundleDualHomStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_pullback_bundle_dual_hom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ' : B ⟶ o.A), IsAbelianScheme B → IsMonHom ψ' → ∃ (C : Over Y) (_ : GrpObj C) (Q : LB (B ⊗ C).left) (h : B ⟶ C), IsAbelianScheme C ∧ GlobalTheory.AbDual.IsDual B C Q ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) ∧ IsMonHom h ∧ LBIso (o.P.pull (ψ' ⊗ₘ ψ').left) (Q.pull (lift (fst B B) (snd B B ≫ h)).left) ∧ ∀ (T : Over Y) (x : T ⟶ B), PullPolTriv o ψ' x ↔ x ≫ h = 1 := by
  first | (exact @GlobalTheory.UPel.HT.ES.pullPol_dual_hom) | (exact GlobalTheory.UPel.HT.ES.pullPol_dual_hom) | (intros; apply GlobalTheory.UPel.HT.ES.pullPol_dual_hom  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSemiAbelianUniformisation_of_finiteExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), HasFin D → Has D := by
  first | exact @GlobalTheory.Mum.has_of_hasFin | exact GlobalTheory.Mum.has_of_hasFin | (intros; apply GlobalTheory.Mum.has_of_hasFin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareDeRhamDualityAbelianSchemeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareDeRhamDuality_abelianScheme : GlobalTheory.Published.PoincareDeRhamDuality := by
  first | exact @GlobalTheory.poincareDeRhamDuality | exact GlobalTheory.poincareDeRhamDuality | (intros; apply GlobalTheory.poincareDeRhamDuality <;> assumption)
end

