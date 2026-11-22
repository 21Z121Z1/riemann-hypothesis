import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0401
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0376
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0404
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyOneCechCocycleOfPullbackZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0352
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupHypercohomologyPullbackStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_hypercohomologyPullback : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ} (hk : n + m = k) a b, cpull ((chains R).map f) K k (μ.cup E' hk a b) = μ.cup E hk (cpull ((chains R).map f) I n a) (cpull ((chains R).map f) J m b) := by
  first | (exact @GlobalTheory.EtC.Pair.cup_pull) | (exact GlobalTheory.EtC.Pair.cup_pull) | (intros; apply GlobalTheory.EtC.Pair.cup_pull  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductCastMkOfIsAlexanderWhitney
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

namespace GlobalTheory.PBFc

theorem cup_cast_mk_of_isAW_rec (q : ℕ) {S : Spc} (a b k n m N : ℤ) (e : a + b = k) (hN : n + m = N)
    (α : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q a)) n)
    (β : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q b)) m)
    (γ : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q k)) N)
    (h : (Eq.rec (motive := fun k _ => Pair (res (ZMod q) (tw q a)) (res (ZMod q) (tw q b)) (res (ZMod q) (tw q k)))
      (twPair q a b) e).IsAW hN α.1 β.1 γ.1) :
    ((cup q (CohomologyClass.mk α) (CohomologyClass.mk β)).cast hN e : Ht q S N k) = CohomologyClass.mk γ := by
  subst e
  subst hN
  exact Pair.cup_spec (twPair q a b) S rfl α β γ h

theorem cup_cast_mk_of_isAW : ∀ (q : ℕ) {S : Spc} (i : ℤ) (j : ℕ) (m : ℤ) (α : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q (i - (j : ℤ)))) (m - 2 * (j : ℤ))) (β : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q (j : ℤ))) (2 * (j : ℤ))) (γ : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q i)) m), (twPairI q i (j : ℤ)).IsAW (sub_add_cancel m _) α.1 β.1 γ.1 → ((cup q (CohomologyClass.mk α) (CohomologyClass.mk β)).cast (by ring) (by ring) : Ht q S m i) = CohomologyClass.mk γ := by
  intro q S i j m α β γ h
  exact cup_cast_mk_of_isAW_rec q (i - (j : ℤ)) (j : ℤ) i (m - 2 * (j : ℤ)) (2 * (j : ℤ)) m
    (sub_add_cancel i _) (sub_add_cancel m _) α β γ h

end GlobalTheory.PBFc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductDiscreteSpaceFibreEqPairing
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.DiscCup

theorem sub_zero_full {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have : SimplexCategory.subinterval 0 N h = 𝟙 _ := by
    ext i; simp [SimplexCategory.subinterval]
  simp [Sx.sub, this]

theorem map_fst_sub {F : PSh} {E' : Spc} {N : ℕ} {U : Scheme.{0}} (w : Sx (disc.obj F ⨯ E') N U) (l : ℕ) (h : 0 + l ≤ N) :
    (show F.obj (op U) from Sx.map (prod.fst : disc.obj F ⨯ E' ⟶ _) (w.sub 0 l h)) =
      (show F.obj (op U) from Sx.map (prod.fst : disc.obj F ⨯ E' ⟶ _) w) := by
  unfold Sx.map Sx.sub
  have h1 := (prod.fst : disc.obj F ⨯ E' ⟶ _).naturality (SimplexCategory.subinterval 0 l h).op
  have h2 := congrArg (fun φ => φ.app (op U)) h1
  simp only [NatTrans.comp_app] at h2
  exact (congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)) h2) w)

theorem ev_vanish {E : Spc} {R : Type} [CommRing R] {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (hv : α.v (-(p : ℤ)) s h = 0) (U : Scheme.{0}) (x : Sx E p U) : ev α p s h U x = 0 := by
  rw [CupSpec.ev_def, hv, comp_zero]
  rfl

end GlobalTheory.EtC.DiscCup

namespace GlobalTheory.EtC.DiscCup

theorem term_zero {q : ℕ} {E₁ E₂ : Spc} {i₁ i₂ n m s : ℤ} (k : ℕ)
    (a : Cochain ((chains (ZMod q)).obj E₁) (res (ZMod q) (tw q i₁)) n)
    (b : Cochain ((chains (ZMod q)).obj E₂) (res (ZMod q) (tw q i₂)) m) (V : Scheme.{0})
    (p : ℕ) (hp : p = 0) (s₁ t₁ : ℤ) (hs₁ : -(p : ℤ) + n = s₁) (ht₁ : -((k - p : ℕ) : ℤ) + m = t₁) (hw : s₁ + t₁ = s)
    (x0 : Sx E₁ p V) (x1 : Sx E₂ (k - p) V) (y0 : Sx E₁ 0 V) (y1 : Sx E₂ k V)
    (h0 : ∀ e : p = 0, e ▸ x0 = y0) (h1 : ∀ e : k - p = k, e ▸ x1 = y1) (hs' : n + (-(k : ℤ) + m) = s) :
    (twPair q i₁ i₂).mul V s₁ t₁ s hw (ev a p s₁ hs₁ V x0) (ev b (k - p) t₁ ht₁ V x1) =
      (twPair q i₁ i₂).mul V n (-(k : ℤ) + m) s hs' (ev a 0 n (by simp) V y0) (ev b k (-(k : ℤ) + m) rfl V y1) := by
  subst hp
  have e0 := h0 rfl
  have e1 := h1 rfl
  subst e0 e1
  obtain rfl : s₁ = n := by omega
  subst ht₁
  rfl

end GlobalTheory.EtC.DiscCup

open GlobalTheory.EtC.DiscCup in
theorem GlobalTheory.EtC.disc_cup_fibre : ∀ (q N : ℕ) (F : PSh) {n m i₁ i₂ : ℤ} (α : Cocycle ((chains (ZMod q)).obj (disc.obj F)) (res (ZMod q) (tw q i₁)) n) (z : Cocycle ((chains (ZMod q)).obj (fibQ q N)) (res (ZMod q) (tw q i₂)) m), (∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), α.1.v (-(p : ℤ)) s h = 0) → ∃ γ : Cocycle ((chains (ZMod q)).obj (disc.obj F ⨯ fibQ q N)) (res (ZMod q) (tw q (i₁ + i₂))) (n + m), CohomologyClass.mk γ = cup q (pull _ (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (CohomologyClass.mk α)) (pull _ (prod.snd : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (CohomologyClass.mk z)) ∧ ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + (n + m) = s) (V : Scheme.{0}) (w : Sx (disc.obj F ⨯ fibQ q N) k V), ev γ.1 k s hs V w = (twPair q i₁ i₂).mul V n (-(k : ℤ) + m) s (by omega) (ev α.1 0 n (by simp) V (show Sx (disc.obj F) 0 V from Sx.map (p := k) (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) w)) (ev z.1 k (-(k : ℤ) + m) rfl V (Sx.map prod.snd w)) := by
  intro q N F n m i₁ i₂ α z hα
  let α' := zcomp (Cocycle.ofHom ((chains (ZMod q)).map (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _))) α (zero_add n)
  let z' := zcomp (Cocycle.ofHom ((chains (ZMod q)).map (prod.snd : disc.obj F ⨯ fibQ q N ⟶ _))) z (zero_add m)
  obtain ⟨γ, hγ⟩ := (twPair q i₁ i₂).aw_exists (disc.obj F ⨯ fibQ q N) rfl α' z'
  refine ⟨γ, ((twPair q i₁ i₂).cup_spec _ rfl α' z' γ hγ).symm, ?_⟩
  intro k s hs V w
  rw [hγ k s hs V w, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
  · have e1 : ((m * (((0 : Fin (k + 1)) : ℕ) : ℤ)).negOnePow) = 1 := by simp
    rw [e1, one_smul]
    change (twPair q i₁ i₂).mul V _ _ s _ (ev ((Cochain.ofHom _).comp α.1 (zero_add n)) _ _ rfl V _)
      (ev ((Cochain.ofHom _).comp z.1 (zero_add m)) _ _ rfl V _) = _
    rw [CupSpec.ev_pull, CupSpec.ev_pull]
    apply term_zero k α.1 z.1 V _ (by simp)
    · intro e
      exact map_fst_sub w _ _
    · intro e
      exact congrArg (Sx.map prod.snd) (sub_zero_full w _)
  · intro i _
    change _ • (twPair q i₁ i₂).mul V _ _ s _ (ev ((Cochain.ofHom _).comp α.1 (zero_add n)) _ _ rfl V _) _ = 0
    rw [CupSpec.ev_pull, ev_vanish α.1 (i.succ : ℕ) _ _ (hα _ (by simp) _ _), map_zero, LinearMap.zero_apply, smul_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegZeroCocycleExistsCoboundaryOfRichBasedStatement
section
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degZeroCocycle_exists_coboundary_of_rich_based : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → K.Based → ∀ (h : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∃ G : C0 K.Oc, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → h T T' φ = G T' - φ.φ (G T) := by
  first | exact @GlobalTheory.AnPer.Charts.DegZero.exists_gauge | exact GlobalTheory.AnPer.Charts.DegZero.exists_gauge | (intros; apply GlobalTheory.AnPer.Charts.DegZero.exists_gauge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthGeThreeFiniteEtalePuncturedRegularStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depth_ge_three_finite_etale_punctured_regular : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], IsAdicComplete (maximalIdeal R) R → 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R, f ∉ maximalIdeal R ^ 2 → ∀ [IsLocalRing (R ⧸ Ideal.span {f})], GlobalTheory.PurityFree (R ⧸ Ideal.span {f}) → ∀ (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], ReciprocityTheory.CA.ModDepthGE R A 2 → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ReciprocityTheory.CA.ModDepthGE R A 3 := by
  first | exact @GlobalTheory.LocalLefschetz.depth_three | exact GlobalTheory.LocalLefschetz.depth_three | (intros; apply GlobalTheory.LocalLefschetz.depth_three <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetOneSubOffDiagonalBlockGramLeOneBallStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detOneSubOffDiagonalBlockGram_le_one_ball : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (X.p0 = 1 ∨ X.p0 + 1 = r) → ∀ z : V (nd X), z ∈ Om X → ∀ τ : X.Ψ, zDet X z τ ≤ 1 := by
  first | exact @GlobalTheory.IntBall.zDet_le_one | exact GlobalTheory.IntBall.zDet_le_one | (intros; apply GlobalTheory.IntBall.zDet_le_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteGlBundleEqTrivialGLBundleStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_glBundle_eq_trivialGLBundle : ∀ (N : ℕ) (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)), V = trivV N (disc.obj F) := by
  first | (exact @GlobalTheory.EtC.disc_eq_trivV) | (exact GlobalTheory.EtC.disc_eq_trivV) | (intros; apply GlobalTheory.EtC.disc_eq_trivV  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnlargeBaseSeparablePointIntegralClosure
section
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginEnlargePoint

theorem enlarge_point : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ GlobalTheory.KeyOriginEnlarge.PointAtZero A' (Localization.AtPrime QA') DA' ρ') ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  intro T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH hP q hq hqT A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _ actA hFits ρ hRet
  obtain ⟨hi, _hil, _hqA, _hQA, _hjA, _hψA, hTor⟩ := hFits
  have hu : ∀ y : Algebra.algebraMapSubmonoid (Localization.AtPrime QA) (nonZeroDivisors A),
      IsUnit (((algebraMap A (FractionRing A)).comp ρ) (y : Localization.AtPrime QA)) := by
    rintro ⟨y, a, ha, rfl⟩
    have h1 : ρ (algebraMap A (Localization.AtPrime QA) a) = a := by
      simpa using congrArg (fun f => f a) hRet.1
    simp only [RingHom.comp_apply, h1]
    exact IsLocalization.map_units (FractionRing A) (⟨a, ha⟩ : nonZeroDivisors A)
  let ρK : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* FractionRing A := IsLocalization.lift hu
  have hρK : ρK.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
      (algebraMap A (FractionRing A)).comp ρ := IsLocalization.lift_comp hu
  obtain ⟨L, _, _, _, _, σL, hσL⟩ := GlobalTheory.T.zmodTorsor_exists_point_finite_separable _ (FractionRing A) ρK DA q hq actA hTor
  obtain ⟨A₁, _, _, _, _, _, _, j, i₁, hj, hi₁, hl₁, hji, κ, hκ⟩ := GlobalTheory.T.exists_normal_local_between_alt T hAIC A i hi L
  obtain ⟨EA₁, _, _, _, _, _, QA₁, _, jA₁, ψA₁, DA₁, _, _, actA₁, ρ₁, hF₁, hR₁, β, h, hβ, hh, hσ⟩ :=
    GlobalTheory.T.exists_baseChange_fittingDatum_retraction T O P φ hφ hSH hP q hq A i EA QA jA ψA DA actA ⟨hi, _hil, _hqA, _hQA, _hjA, _hψA, hTor⟩ ρ hRet
      A₁ j i₁ hj hi₁ hl₁ hji
  obtain ⟨σ₁, hσ₁⟩ := hσ (κ.comp σL) (by
    ext x
    have h1 := congrArg (fun f => f (algebraMap (Localization.AtPrime QA)
      (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) x)) hσL
    have h2 := congrArg (fun f => f x) hρK
    have h3 := congrArg (fun f => f (ρ x)) hκ
    simp only [RingHom.comp_apply] at h1 h2 h3 ⊢
    rw [h1, h2, h3])
  refine ⟨A₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, i₁,
    EA₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, QA₁, inferInstance, jA₁, ψA₁,
    DA₁, inferInstance, inferInstance, actA₁, hF₁, ⟨ρ₁, hR₁, ?_⟩, β, h, hβ, hh⟩
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A₁ (Localization.AtPrime QA₁) DA₁
  refine ⟨σ₁.comp (GlobalTheory.KeyOriginNoeth.closure A₁ (Localization.AtPrime QA₁) DA₁).subtype, ?_⟩
  ext r
  exact congrArg (fun f => f r) hσ₁

end GlobalTheory.KeyOriginEnlargePoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmPowTwelveDivDiscriminantMemSubringStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.esymm_pow_twelve_div_discriminant_mem_subring : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (R : Subring ℂ) (τ₀ : ℍ), 0 < N → ActBij act → IsFam act w f → (∀ i, QAll (· ∈ R) N (f i)) → jT τ₀ ∈ R → ∀ k : ℕ, (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ₀ ^ 12 / DD τ₀ ^ w) ∈ R := by
  first | exact @GlobalTheory.QFam.esymm_pow_twelve_div_mem | exact GlobalTheory.QFam.esymm_pow_twelve_div_mem | (intros; apply GlobalTheory.QFam.esymm_pow_twelve_div_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyOneCechCocycleOfPullbackZeroStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_one_cechCocycle_of_pullback_zero : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (x : H R (sch.obj X) F 1), pull R (sch.map f) F 1 x = 0 → ∃ s : (free R).obj ((cech f).obj (op (SimplexCategory.mk (1)))) ⟶ F, cobd s = 0 ∧ IsCls s (pull R (cechAug f) F 1 x) := by
  first | exact @GlobalTheory.EtC.LerayOne.cech_cocycle_of_pull_eq_zero | exact GlobalTheory.EtC.LerayOne.cech_cocycle_of_pull_eq_zero | (intros; apply GlobalTheory.EtC.LerayOne.cech_cocycle_of_pull_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProdRingProjectionsBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ProdCoh

theorem cpull_bijective_of_isIso {R : Type} [CommRing R] {K L : Cx R} (c : K ⟶ L) [IsIso c] (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull c I n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cpull (inv c) I n, fun x => ?_, fun x => ?_⟩
  · rw [BiprodCls.cpull_cpull, IsIso.inv_hom_id, BiprodCls.cpull_id]
  · rw [BiprodCls.cpull_cpull, IsIso.hom_inv_id, BiprodCls.cpull_id]

theorem bij_of_eq {α β : Sort*} {f g : α → β} (h : ∀ x, f x = g x) (hg : Function.Bijective g) :
    Function.Bijective f := by
  rw [show f = g from funext h]; exact hg

theorem ht_prod_bijective : ∀ (q : ℕ) (A B : Type) [CommRing A] [CommRing B] (n i : ℤ),
    Function.Bijective (fun x : Ht q (sp (A × B)) n i =>
      (pull _ (spMap (RingHom.fst A B)) _ _ x, pull _ (spMap (RingHom.snd A B)) _ _ x)) := by
  intro q A B _ _ n i
  have h2 := GlobalTheory.T.freeEtaleSheaf_biprodDesc_isIso_of_res_bijective (ZMod q) _ _ (GlobalTheory.T.etaleSheafSections_specProd_bijective (ZMod q) A B)
  have h3 := GlobalTheory.T.etaleChains_disc_biprod_desc_isIso (ZMod q) _ _ h2
  have hc := @cpull_bijective_of_isIso _ _ _ _ _ h3 (res (ZMod q) (tw q i)) n
  have := (cpull_biprod_bijective (ZMod q) _ _ (res (ZMod q) (tw q i)) n).comp hc
  refine bij_of_eq (fun x => ?_) this
  dsimp only [Function.comp]
  erw [BiprodCls.cpull_cpull, BiprodCls.cpull_cpull, biprod.inl_desc, biprod.inr_desc]
  rfl

end GlobalTheory.EtC.ProdCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyPullbackEqZeroOfCechOneCocycleStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomologyPullback_eq_zero_of_cechOneCocycle : ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X) (s : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F), cobd s = 0 → ∀ x : H R (sch.obj X) F ((1 : ℕ) : ℤ), IsCls s (pull R (cechAug f) F ((1 : ℕ) : ℤ) x) → pull R (sch.map f) F ((1 : ℕ) : ℤ) x = 0 := by
  first | (exact @GlobalTheory.CechOne.pull_sch_eq_zero) | (exact GlobalTheory.CechOne.pull_sch_eq_zero) | (intros; apply GlobalTheory.CechOne.pull_sch_eq_zero  <;> assumption)
end

