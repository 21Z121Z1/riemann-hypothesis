import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0046
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0047
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyNormalFormDetRatioTwoTorsionTranslate
import Development.AbelianVarietyTheory.Definitions.KeyFormula.SameObj
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_thetaFrameValue_holomorphicFamily : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → ∀ (S : Type) [CommRing S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (y : KeyIn S) (m : ℕ) (B : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (S →ₐ[ℂ] ℂ)) (t : (Fin m → ℂ) → ℂ), IsOpen B → (∀ a : S, DifferentiableOn ℂ (fun p => s p a) B) → (∀ p ∈ B, ∃ x : KeyIn ℂ, KeyPB x y (s p).toRingHom ∧ (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t p = M.det ^ 4 / c ^ 8)) → ContinuousOn t B := by
  first | exact @GlobalTheory.ThetaValueCont.continuousOn_value | exact GlobalTheory.ThetaValueCont.continuousOn_value | (intros; apply GlobalTheory.ThetaValueCont.continuousOn_value <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyDataNearTwoPrimes
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem exists_keyIn_polPB {R R₁ R' : Type} [CommRing R] [CommRing R₁] [CommRing R'] (Q : Out.PolAV (Sp R))
    (hg : 1 ≤ Q.g) (f₁ : R →+* R₁) (g : R₁ →+* R') (f : R →+* R') (hf : g.comp f₁ = f) (th : Q.L.Sec)
    (hth : ∀ s : Sp R', ∃ x : Q.A.left, Q.A.hom x = spMap f s ∧ x ∈ Out.nonzeroLocus th)
    (v : Fin Q.g → (epsR R₁ ⟶ (Over.pullback (spMap f₁)).obj Q.A)) (hv : IsLieBasis v) :
    ∃ (y : KeyIn R') (φ : y.P.A.left ⟶ Q.A.left), PolPB y.P Q (spMap f) φ := by
  have h := isGrpPullback_pullback Q.A (spMap f)
  let φ : ((Over.pullback (spMap f)).obj Q.A).left ⟶ Q.A.left := pullback.fst Q.A.hom (spMap f)
  change IsGrpPullback _ _ _ φ at h
  have hL' := pull_isLB Q.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let P' : Out.PolAV (Sp R') :=
    { A := (Over.pullback (spMap f)).obj Q.A
      isAb := Out.TLinPf.isAb_pullback (spMap f) Q.A Q.isAb
      g := Q.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 Q.smoothDim
      L := Q.L.pull φ
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h Q.rigid
      sym := PolBaseChange.sym_pull h Q.sym
      ample := relAmple_pull h.1 Q.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) Q.ample
      ktriv := kTriv_pull h Q.isLB hL' hw Q.ktriv }
  obtain ⟨rig, hr⟩ := P'.rigid
  obtain ⟨th', hth'⟩ := sec_pull_down hw Q.isLB hL' th
  have h₁ := isGrpPullback_pullback Q.A (spMap f₁)
  have hA₁ := Out.TLinPf.isAb_pullback (spMap f₁) Q.A Q.isAb
  have c₁ := hA₁.comm
  have c₂ : IsCommMonObj P'.A := P'.isAb.comm
  have e : spMap g ≫ spMap f₁ = spMap f := by
    rw [← hf, ← Spec.map_comp]; rfl
  have w : φ ≫ Q.A.hom = P'.A.hom ≫ spMap g ≫ spMap f₁ := by rw [e]; exact h.1.w
  have w₁ : φ ≫ Q.A.hom = (P'.A.hom ≫ spMap g) ≫ spMap f₁ := by rw [Category.assoc]; exact w
  have h₂ : IsGrpPullback P'.A _ (spMap g) (h₁.1.lift _ _ w₁) :=
    IsGrpPullback.cancel h₁ (h.congr e.symm (h₁.1.lift_fst _ _ w₁).symm) (h₁.1.lift_snd _ _ w₁)
  obtain ⟨v', hb', -⟩ := exists_isLieBasis_baseChange R₁ R' g _ P'.A _ h₂ hA₁.smooth Q.g v hv
  refine ⟨⟨P', hg, rig, hr, th', fun s => ?_, v', hb'⟩, φ, h, rfl, ⟨idIso _, idIso_isGen hL'⟩⟩
  obtain ⟨z, hz, hz'⟩ := hth s
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
  refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
  have u₁ : IsUnit (gs φ y _ (th.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
  have e := hth' _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
  rw [Category.id_comp] at e
  exact isUnit_of_mul_isUnit_right (e ▸ u₁)

theorem exists_keyIn_near_two : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Q : Out.PolAV (Sp R)) (p q : PrimeSpectrum R), 1 ≤ Q.g → ∃ r : R, r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∃ (y : KeyIn (Localization.Away r)) (φ : y.P.A.left ⟶ Q.A.left), PolPB y.P Q (spMap (algebraMap R (Localization.Away r))) φ := by
  intro hL hL₂ R _ _ Q p q hg
  obtain ⟨th, a, ap, aq, ha⟩ := GlobalTheory.T.exists_principalPolarization_section_nonzero_near_two_primes hL hL₂ R Q p q
  have c : IsCommMonObj Q.A := Q.isAb.comm
  obtain ⟨b, bp, bq, v, hv⟩ := GlobalTheory.T.exists_lieBasis_away_avoiding_two_primes R Q.A Q.g Q.smoothDim p q
  refine ⟨b * a, fun h => (p.isPrime.mem_or_mem h).elim bp ap, fun h => (q.isPrime.mem_or_mem h).elim bq aq, ?_⟩
  refine exists_keyIn_polPB Q hg (algebraMap R (Localization.Away b))
    (IsLocalization.Away.awayToAwayRight (S := Localization.Away b) (P := Localization.Away (b * a)) b a) _
    (RingHom.ext fun x => IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away b) b a x) th
    (fun s => ha _ fun h => ?_) v hv
  have h' : algebraMap R (Localization.Away (b * a)) a ∈ s.asIdeal := h
  have u : IsUnit (algebraMap R (Localization.Away (b * a)) (b * a)) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at u
  exact s.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (isUnit_of_mul_isUnit_right u))

end GlobalTheory.KeyFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsLocalPeriodMatrix
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.PeriodLift

open GlobalTheory.LocLift GlobalTheory.ThetaValueCont Filter Topology

theorem exists_bilin_omegaStd (g : ℕ) :
    ∃ EF : LinearMap.BilinForm ℤ (Fin g ⊕ Fin g → ℤ), ∀ a b, EF a b = omegaStd a b :=
  ⟨LinearMap.mk₂ ℤ (fun x y => omegaStd x y)
    (fun x x' y => by
      simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun c x y => by
      simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun x y y' => by
      simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun c x y => by
      simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring), fun _ _ => rfl⟩

theorem eq_zero_of_per_eq_zero {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hp : (τ.map Complex.im).PosDef)
    {a : Fin g ⊕ Fin g → ℤ} (h : per τ a = 0) : a = 0 := by
  have h1 : (τ.map Complex.im).mulVec (fun i => (a (.inl i) : ℝ)) = 0 := by
    funext i
    have := congrArg Complex.im (congrFun h i)
    simpa [per, Matrix.mulVec, dotProduct] using this
  have h2 : (fun i => (a (.inl i) : ℝ)) = 0 :=
    Matrix.mulVec_injective_iff_isUnit.2 hp.isUnit (h1.trans (Matrix.mulVec_zero _).symm)
  have h3 : ∀ i, a (.inl i) = 0 := fun i => by simpa using congrFun h2 i
  funext i
  rcases i with i | i
  · exact h3 i
  · simpa [per, h3, Matrix.mulVec, dotProduct] using congrFun h i

theorem perLev_of_periods (hT : ThetaUnifAV) (hmul : Out.MulNSt) (P : Out.PolAV (Sp ℂ)) {g : ℕ} (hg : P.g = g) (k : ℕ)
    (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) (hadd : ∀ z w, e (z + w) = e z * e w)
    (hon : Function.Surjective e) (hol : IsHolTo Set.univ fun z => (e z).left)
    (p : (Fin g ⊕ Fin g → ℤ) →+ (Fin g → ℂ)) (hker : ∀ z, e z = 1 ↔ z ∈ p.range) (hi : Function.Injective p)
    (hs : Submodule.span ℝ (Set.range p) = ⊤) (hd : DiscreteTopology p.range)
    (hweil : ∀ (n : ℕ) (a b : Fin g ⊕ Fin g → ℤ) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / n) →
      Out.WeilIs P.A P.L n (e ((n : ℂ)⁻¹ • p a)) (e ((n : ℂ)⁻¹ • p b)) (unitOn c)) :
    IsUnit (Matrix.of fun i j => p (Pi.single (.inr j) 1) i).det ∧
      PerLev P ((Matrix.of fun i j => p (Pi.single (.inr j) 1) i)⁻¹ * Matrix.of fun i j => p (Pi.single (.inl j) 1) i) k
        fun a => e ((k : ℂ)⁻¹ • p a) := by
  subst hg
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, -, -, hE, -, hW⟩ := hT P rig hrig
  obtain ⟨EF, hEF'⟩ := exists_bilin_omegaStd P.g
  obtain ⟨F, hF⟩ := ThetaPoint.exists_linearEquiv_lift hmul P u e hadd hon hol
    ((Set.countable_range p).mono fun z hz => (hker z).1 hz)
  have hFΛ : ∀ z, F z ∈ u.Λ ↔ z ∈ p.range := fun z => by rw [← u.ker, hF, hker]
  have hEF : ∀ a a₂, (hermForm Hm (F (p a)) (F (p a₂))).im = EF a a₂ := fun a a₂ => by
    refine (hE ⟨_, (hFΛ _).2 ⟨a, rfl⟩⟩ ⟨_, (hFΛ _).2 ⟨a₂, rfl⟩⟩).symm.trans (congrArg _ ?_)
    rw [hEF']
    refine int_eq_of_exp fun k hk => ?_
    have k₁ := hW k ⟨_, (hFΛ _).2 ⟨a, rfl⟩⟩ ⟨_, (hFΛ _).2 ⟨a₂, rfl⟩⟩ (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have k₂ := hweil k a a₂ (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    simp only [← map_smul, hF] at k₁
    exact congrArg Units.val (weilIs_unique_fieldPoint _ P.A P.L P.isLB ℂ (𝟙 _) k _ _ _ _ k₁ k₂)
  obtain ⟨Hm', h1, h2, h3⟩ : HasForm EF p := HasForm.of_comp F.toLinearMap F.injective ⟨Hm, hAH.1, hAH.2.1, hEF⟩
  obtain ⟨h, τ, hh, hinv, hτ, hsy, hp, -, hper⟩ := SiegelPeriod.exists_siegel_form _ EF _ (LinearEquiv.refl ℤ _) p Hm'
    hEF' ⟨hi, hd, hs, h1, h2, h3⟩
  simp only [LinearEquiv.refl_apply] at hinv hτ hper
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hh
  rw [← hinv, Matrix.nonsing_inv_nonsing_inv _ hdet, ← hτ]
  refine ⟨Matrix.isUnit_nonsing_inv_det _ hdet, ?_⟩
  let ψ : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ) := LinearEquiv.ofBijective h.mulVecLin
    ⟨Matrix.mulVec_injective_iff_isUnit.2 hh, Matrix.mulVec_surjective_iff_isUnit.2 hh⟩
  have hψ : ∀ a, ψ.symm (per τ a) = p a := fun a => by
    rw [LinearEquiv.symm_apply_eq]
    exact (hper a).symm
  obtain ⟨u', hex, hΛ, -⟩ := exists_holUnif_reparam P.A P.L P.g u (ψ.symm.trans F) (fun _ => 1)
    (differentiable_const _) (fun _ => one_ne_zero) rfl
  have hex' : ∀ (c : ℂ) a, u'.ex (c • per τ a) = e (c • p a) := fun c a => by
    rw [hex, LinearEquiv.trans_apply, hF, map_smul, hψ]
  refine ⟨rfl, hsy, hp, u', fun z => ?_, fun n a b c hn hc => ?_, fun a => (hex' _ a).symm⟩
  · rw [hΛ, LinearEquiv.trans_apply, hFΛ]
    refine exists_congr fun a => ?_
    rw [← hψ, ψ.symm.injective.eq_iff, eq_comm]
  · rw [hex', hex']
    exact hweil n a b c hn hc

theorem exists_local_period_matrix : Out.Laws → ThetaUnifAV → ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (Q : Out.PolAV X) (g k m : ℕ) (l : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over X) ⟶ Q.A)) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (P₀ : Out.PolAV (Sp ℂ)) (φ₀ : P₀.A.left ⟶ Q.A.left) (τ₀ : Matrix (Fin g) (Fin g) ℂ) (lev₀ : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P₀.A)), LocallyOfFiniteType s → 0 < k → (∀ a, l a ^ k = 1) → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → PolPB P₀ Q (y b₀) φ₀ → PerLev P₀ τ₀ k lev₀ → (∀ a, (lev₀ a).left ≫ φ₀ = y b₀ ≫ (l a).left) → ∃ (B' : Set (Fin m → ℂ)) (τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ τ b₀ = τ₀ ∧ (∀ i j, DifferentiableOn ℂ (fun b => τ b i j) B') ∧ ∀ b ∈ B', ∃ (P : Out.PolAV (Sp ℂ)) (φ : P.A.left ⟶ Q.A.left) (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), PolPB P Q (y b) φ ∧ PerLev P (τ b) k lev ∧ ∀ a, (lev a).left ≫ φ = y b ≫ (l a).left := by
  intro hL hT K _ σ X s Q g k m l B y b₀ P₀ φ₀ τ₀ lev₀ hft hk hl0 hB hb₀ hyσ hy ⟨hφ₀, hg₀, hL₀⟩
    ⟨hg, _, hp₀, u, hΛ, w₀, hlev₀⟩ hlev
  subst hg
  haveI : CharZero K := σ.charZero
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI := Q.isAb.proper
  obtain ⟨Φ₀, hΦ₀, hΦW₀⟩ := exists_push_iff Q P₀ hφ₀ hL₀
  have he₀ : IsExp (y b₀) fun z => Φ₀ (u.ex z) := by
    obtain ⟨rig, hrig⟩ := P₀.rigid
    obtain ⟨u₀, -, -, -, -, -, h₁, h₂, -⟩ := hT P₀ rig hrig
    obtain ⟨F, hF⟩ := ThetaPoint.exists_linearEquiv_lift hL.mulN P₀ u₀ u.ex u.ex_add u.ex_onto
      (fun U f => by simpa using u.hol U f) ((Set.countable_range (per τ₀)).mono fun z hz => by
        obtain ⟨a, ha⟩ := (hΛ z).1 ((u.ker z).1 hz)
        exact ⟨a, ha.symm⟩)
    have := (PointUnif.isExp_push hφ₀ u₀ h₁ h₂ Φ₀ hΦ₀).comp_equiv F
    simp only [hF] at this
    exact this
  obtain ⟨B₁, e, r, hB₁, hb₁, hB₁B, he0, hr, hol, he, hl⟩ := RelExp.exists_relative_exp K σ X s Q.A P₀.g m B y b₀
    (fun z => Φ₀ (u.ex z)) hft Q.isAb (hg₀ ▸ Q.smoothDim) hB hb₀ hyσ hy he₀
  change HasLifts B₁ y e at hl
  change ∀ b ∈ B₁, IsExp (y b) (e b) ∧ _ at he
  have hy₁ := isHolTo_mono hy hB₁ hB₁B
  let p₀ : (Fin P₀.g ⊕ Fin P₀.g → ℤ) →+ (Fin P₀.g → ℂ) := AddMonoidHom.mk' (per τ₀) (per_add τ₀)
  have hrange : Set.range p₀ = u.Λ := Set.ext fun z => by
    rw [SetLike.mem_coe, hΛ]
    exact exists_congr fun a => eq_comm
  obtain ⟨P, hP₀, hP⟩ := exists_periods latContinuation hB₁ hb₁ hy₁ hr hol he hl p₀
    ((injective_iff_map_eq_zero p₀).2 fun a ha => eq_zero_of_per_eq_zero hp₀ ha) (hrange ▸ u.full) (fun z => by
      rw [he0]
      exact (map_eq_one_iff Φ₀ Φ₀.injective).trans ((u.ker z).trans (Set.ext_iff.1 hrange z).symm))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hP.and (hB₁.mem_nhds hb₁))
  set C := Metric.ball b₀ ε
  have hCo : IsOpen C := Metric.isOpen_ball
  have hCc : IsPreconnected C := (convex_ball b₀ ε).isPreconnected
  have hC₀ : b₀ ∈ C := Metric.mem_ball_self hε
  have hC₁ : C ⊆ B₁ := fun b hb => (hball b hb).2
  have hPd : ∀ x, DifferentiableOn ℂ (fun b => P b x) C := fun x b hb => ((hball b hb).1.1 x).differentiableWithinAt
  have hk1 : ∀ b ∈ C, ∀ x, e b (P b x) = 1 := fun b hb x => ((hball b hb).1.2.1 _).2 ⟨x, rfl⟩
  have htor : ∀ (k : ℕ) x, IsHolTo C (fun b => (e b ((k : ℂ)⁻¹ • P b x)).left) := fun k x =>
    isHolTo_comp (β := fun b => (b, (k : ℂ)⁻¹ • P b x)) hol hCo
      (differentiableOn_id.prodMk ((hPd x).fun_const_smul _)) fun b hb => ⟨hC₁ hb, trivial⟩
  have hpow : ∀ (k : ℕ), 0 < k → ∀ x, ∀ b ∈ C, e b ((k : ℂ)⁻¹ • P b x) ^ k = 1 := fun k hk x b hb => by
    rw [← hom_nsmul (he b (hC₁ hb)).1.1, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 hk.ne'),
      hk1 b hb]
  have hwe : ∀ b ∈ C, ∀ (k : ℕ) (a a₂ : Fin P₀.g ⊕ Fin P₀.g → ℤ) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a a₂ : ℂ) / k) →
      Out.WeilIs Q.A Q.L k (e b ((k : ℂ)⁻¹ • P b a)) (e b ((k : ℂ)⁻¹ • P b a₂)) (unitOn c) :=
    fun b hb k a a₂ c hk hc => (torsion_eq_and_weilIs_of_isHolTo hL X Q m k C y
      (fun b => e b ((k : ℂ)⁻¹ • P b a)) (fun b => e b ((k : ℂ)⁻¹ • P b a₂)) c b₀ hk
      (isUnit_natCast_of_over s hk) hCo hCc hC₀ (htor k a) (htor k a₂)
      fun b hb => ⟨hpow k hk a b hb, hpow k hk a₂ b hb⟩).2
        (by rw [hP₀, he0]; exact (hΦW₀ _ _ _ _).1 (w₀ k a a₂ c hk hc)) b hb
  have hleft : ∀ a b, (toUnit (Over.mk (y b)) ≫ l a).left = y b ≫ (l a).left := fun a b => by
    rw [Over.comp_left, Over.toUnit_left]; rfl
  have hsec : ∀ a, ∀ b ∈ C, toUnit _ ≫ l a = e b ((k : ℂ)⁻¹ • P b a) :=
    fun a => (torsion_eq_and_weilIs_of_isHolTo hL X Q m k C y (fun b => toUnit _ ≫ l a)
      (fun b => e b ((k : ℂ)⁻¹ • P b a)) 1 b₀ hk (isUnit_natCast_of_over s hk) hCo hCc hC₀
      (isHolTo_congr (isHolTo_comp_hom (isHolTo_mono hy₁ hCo hC₁) (l a).left) fun b _ => hleft a b) (htor k a)
      fun b hb => ⟨by rw [← MonObj.comp_pow, hl0, MonObj.comp_one], hpow k hk a b hb⟩).1 (by
        rw [hP₀, he0]
        refine Over.OverMorphism.ext ?_
        rw [hleft, ← hlev, hlev₀]
        exact (hΦ₀ _).symm)
  have fib : ∀ b ∈ C, IsUnit (Matrix.of fun i j => P b (Pi.single (.inr j) 1) i).det ∧
      ∃ (A : Out.PolAV (Sp ℂ)) (φ : A.A.left ⟶ Q.A.left)
        (lev : (Fin P₀.g ⊕ Fin P₀.g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ A.A)), PolPB A Q (y b) φ ∧
        PerLev A ((Matrix.of fun i j => P b (Pi.single (.inr j) 1) i)⁻¹ *
          Matrix.of fun i j => P b (Pi.single (.inl j) 1) i) k lev ∧
        ∀ a, (lev a).left ≫ φ = y b ≫ (l a).left := fun b hb => by
    obtain ⟨A, φ, hφ, hgA, hm, t, ht⟩ := hL.polBaseChange _ _ (y b) Q
    have hgp : IsGrpPullback A.A Q.A (y b) φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
      rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
      rfl⟩
    have hLA : LBIso A.L (Q.L.pull φ) := LBIso.symm ⟨t, ht⟩
    obtain ⟨Φ, hΦ, hΦW⟩ := exists_push_iff Q A hgp hLA
    have h₁ : ∀ z, (Φ.symm (e b z)).left ≫ φ = (e b z).left := fun z => by rw [← hΦ, Φ.apply_symm_apply]
    have hex := (he b (hC₁ hb)).1
    obtain ⟨q1, q2⟩ := perLev_of_periods hT hL.mulN A (hgA.trans hg₀.symm) k (fun z => Φ.symm (e b z))
      (fun z w => by rw [hex.1, map_mul]) (Φ.symm.surjective.comp hex.2.1)
      (ThetaPoint.isHolTo_fibre hφ _ (fun z => Over.w (Φ.symm (e b z))) (by simpa only [h₁] using hex.2.2.1)) (P b)
      (fun z => (map_eq_one_iff _ Φ.symm.injective).trans ((hball b hb).1.2.1 z)) (hball b hb).1.2.2.1
      (hball b hb).1.2.2.2.1 (hball b hb).1.2.2.2.2 fun n a a₂ c hn hc => by
        rw [hΦW, Φ.apply_symm_apply, Φ.apply_symm_apply]
        exact hwe b hb n a a₂ c hn hc
    exact ⟨q1, A, φ, _, ⟨hgp, hgA, hLA⟩, q2, fun a => by rw [h₁, ← hsec a b hb, hleft]⟩
  refine ⟨C, fun b => (Matrix.of fun i j => P b (Pi.single (.inr j) 1) i)⁻¹ *
    Matrix.of fun i j => P b (Pi.single (.inl j) 1) i, hCo, hC₀, hC₁.trans hB₁B, ?_, fun i j => ?_,
    fun b hb => (fib b hb).2⟩
  · have e1 : (Matrix.of fun i j => P b₀ (Pi.single (.inr j) 1) i) = 1 := by
      ext i j
      simp [hP₀, p₀, per, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply]
    beta_reduce
    rw [e1, inv_one, Matrix.one_mul]
    ext i j
    simp [hP₀, p₀, per, Matrix.mulVec, dotProduct, Pi.single_apply]
  · have dh : ∀ i j, DifferentiableOn ℂ (fun b => (Matrix.of fun i j => P b (Pi.single (.inr j) 1) i)⁻¹ i j) C :=
      ThetaFamily.differentiableOn_left_inverse (fun i k => differentiableOn_pi.1 (hPd _) i)
        fun b hb => Matrix.nonsing_inv_mul _ (fib b hb).1
    simp only [Matrix.mul_apply]
    exact DifferentiableOn.fun_sum fun l _ => (dh i l).fun_mul (differentiableOn_pi.1 (hPd _) l)

end GlobalTheory.PeriodLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsThetaKeyDatumKnownValueRatStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaKeyDatum_known_value_rat : Out.Laws → ThetaUnifAV → ∀ g : ℕ, 1 ≤ g → ∃ y : KeyIn ℚ, y.P.g = g ∧ Known ℚ y := by
  first | exact @GlobalTheory.KeyFam.exists_known_rat | exact GlobalTheory.KeyFam.exists_known_rat | (intros; apply GlobalTheory.KeyFam.exists_known_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsThetaKeyFamilyUniversalFramesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaKeyFamily_universal_frames : Out.Laws → ∀ (k S : Type) [Field k] [CommRing S] [Algebra k S] (y : KeyIn S) (x : KeyIn ℂ) (s : S →+* ℂ) (φ : x.P.A.left ⟶ y.P.A.left) (s₀ : S →ₐ[k] k), GeomInt k S → PolPB x.P y.P (spMap s) φ → ∃ (S' : Type) (_ : CommRing S') (_ : Algebra k S') (j : S →ₐ[k] S') (y' : KeyIn S') (s' : S' →+* ℂ) (s₀' : S' →ₐ[k] k) (ψ : y'.P.A.left ⟶ y.P.A.left), GeomInt k S' ∧ KeyPB x y' s' ∧ PolPB y'.P y.P (spMap j.toRingHom) ψ ∧ s₀'.comp j = s₀ := by
  first | exact @GlobalTheory.KeyFam.exists_univ_frames | exact GlobalTheory.KeyFam.exists_univ_frames | (intros; apply GlobalTheory.KeyFam.exists_univ_frames <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyNormalFormDetRatioTwoTorsionTranslateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyNormalFormDetRatio_twoTorsion_translate : Out.Laws → ThetaUnifAV → ∀ (x x' : KeyIn ℂ) (p : 𝟙_ (Over (Sp ℂ)) ⟶ x.P.A) (ν : ℂˣ) (t : ℂ), IsTrl x' x p ν → Val x t → Val x' (t * (ν : ℂ) ^ 2) := by
  first | exact @GlobalTheory.KeyEq.val_of_isTrl | exact GlobalTheory.KeyEq.val_of_isTrl | (intros; apply GlobalTheory.KeyEq.val_of_isTrl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RingKrullDimLocalizationQuotientLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem ringKrullDim_localization_quotient_le {R : Type} [CommRing R] {k : ℕ} (f : Fin k → R) (m : Ideal R)
    [m.IsPrime] :
    ringKrullDim (Localization.AtPrime m ⧸
        Ideal.span (Set.range fun j => algebraMap R (Localization.AtPrime m) (f j))) ≤
      topologicalKrullDim (PrimeSpectrum.zeroLocus (Set.range f) : Set (PrimeSpectrum R)) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  have h₁ := (PrimeSpectrum.localization_comap_isInducing (R := R) (Localization.AtPrime m) m.primeCompl).comp
    (PrimeSpectrum.isEmbedding_comap_of_surjective _ (Ideal.Quotient.mk
      (Ideal.span (Set.range fun j => algebraMap R (Localization.AtPrime m) (f j))))
      Ideal.Quotient.mk_surjective).isInducing
  refine (h₁.codRestrict (s := PrimeSpectrum.zeroLocus (Set.range f)) fun p => ?_).topologicalKrullDim_le
  rintro _ ⟨j, rfl⟩
  change Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime m) (f j)) ∈ p.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self (f := fun j => algebraMap R (Localization.AtPrime m) (f j)) j))]
  exact p.asIdeal.zero_mem

theorem ofList_take_ofFn {R : Type} [CommRing R] {g : ℕ} (f : Fin g → R) (i : ℕ) :
    Ideal.ofList ((List.ofFn f).take i) = Ideal.span (f '' {j | j.val < i}) := by
  unfold Ideal.ofList
  congr 1
  ext a
  simp only [Set.mem_setOf_eq, List.mem_take_iff_getElem, List.length_ofFn, List.getElem_ofFn, Set.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, by omega⟩, by simp only; omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by have := j.2; omega, rfl⟩

theorem isWeaklyRegular_of_dim_zeroLocus {R : Type} [CommRing R] {g : ℕ} (f : Fin g → R)
    (hreg : ∀ (m : Ideal R) [m.IsMaximal],
      IsRegularLocalRing (Localization.AtPrime m) ∧ ringKrullDim (Localization.AtPrime m) = g)
    (hdim : ∀ (k : ℕ) (hk : k ≤ g),
      (PrimeSpectrum.zeroLocus (Set.range fun j => f (Fin.castLE hk j)) : Set (PrimeSpectrum R)).Nonempty →
      topologicalKrullDim (PrimeSpectrum.zeroLocus (Set.range fun j => f (Fin.castLE hk j)) :
        Set (PrimeSpectrum R)) ≤ ((g - k : ℕ) : WithBot ℕ∞)) :
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f) := by
  refine ⟨fun i hi => ?_⟩
  have hi' : i < g := by simpa using hi
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem, ofList_take_ofFn, List.getElem_ofFn]
  simp only [smul_eq_mul, Ideal.mul_top]
  intro a ha
  refine Ideal.mem_of_localization_maximal fun m hm => ?_
  have ha' := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime m)) ha
  rw [map_mul] at ha'
  by_cases hall : ∀ j : Fin g, j.val ≤ i → f j ∈ m
  · obtain ⟨h₁, h₂⟩ := hreg m
    have hk : i + 1 ≤ g := hi'
    have hd := (ringKrullDim_localization_quotient_le (fun j => f (Fin.castLE hk j)) m).trans
      (hdim (i + 1) hk ⟨⟨m, hm.isPrime⟩, by
        rintro _ ⟨j, rfl⟩
        exact hall _ (by have := j.2; simp only [Fin.val_castLE]; omega)⟩)
    have hr := GlobalTheory.isRegular_ofFn_of_ringKrullDim_quotient_add_le (Localization.AtPrime m) g (i + 1)
      (fun j => algebraMap R (Localization.AtPrime m) (f (Fin.castLE hk j))) h₂
      (fun j => (IsLocalization.AtPrime.to_map_mem_maximal_iff _ m _).2
        (hall _ (by have := j.2; simp only [Fin.val_castLE]; omega)))
      ((add_le_add_left hd _).trans (by
        rw [← Nat.cast_add, Nat.sub_add_cancel hk]))
    have h₃ := hr.toIsWeaklyRegular.regular_mod_prev i (by simp)
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem, ofList_take_ofFn, List.getElem_ofFn] at h₃
    simp only [smul_eq_mul, Ideal.mul_top] at h₃
    have e : Ideal.map (algebraMap R (Localization.AtPrime m)) (Ideal.span (f '' {j | j.val < i})) =
        Ideal.span ((fun j : Fin (i + 1) => algebraMap R (Localization.AtPrime m) (f (Fin.castLE hk j))) ''
          {j | j.val < i}) := by
      rw [Ideal.map_span]
      congr 1
      ext b
      constructor
      · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        exact ⟨⟨j, Nat.lt_succ_of_lt hj⟩, hj, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨_, ⟨Fin.castLE hk j, hj, rfl⟩, rfl⟩
    rw [e] at ha' ⊢
    exact h₃ _ ha'
  · push Not at hall
    obtain ⟨j, hj, hjm⟩ := hall
    have hu : IsUnit (algebraMap R (Localization.AtPrime m) (f j)) :=
      IsLocalization.map_units _ (⟨f j, hjm⟩ : m.primeCompl)
    rcases hj.eq_or_lt with hj | hj
    · subst hj
      exact (Ideal.unit_mul_mem_iff_mem _ hu).1 ha'
    · rw [Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_image_of_mem f (show j ∈ {j : Fin g | j.val < i} from hj)))) hu]
      trivial

theorem isWeaklyRegular_of_finZ : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n : ℕ) (s : Fin x.P.g → RR x n) (V : x.P.A.left.Opens) (c : x.P.L.ι) (h : V ≤ x.P.L.U c), 1 ≤ n → FinZ x s → IsAffineOpen V → RingTheory.Sequence.IsWeaklyRegular Γ(x.P.A.left, V) (List.ofFn fun i => resG x.P.A.left h ((s i).f c)) := by
  intro hL K _ _ x n s V c h hn hZ hV
  refine isWeaklyRegular_of_dim_zeroLocus _ (fun m _ => ?_) fun k hk hne => ?_
  · exact GlobalTheory.isRegularLocalRing_and_ringKrullDim_eq_of_polAV K x.P Γ(x.P.A.left, V) hV.fromSpec m _ inferInstance
  · let W : Set x.P.A.left := {y | ∀ j : Fin k, y ∉ Out.nonzeroLocus (s (Fin.castLE hk j))}
    have hW : IsClosed W := by
      have : W = ⋂ j : Fin k, (Out.nonzeroLocus (s (Fin.castLE hk j)) : Set x.P.A.left)ᶜ := by
        ext y; simp [W]
      rw [this]
      exact isClosed_iInter fun j => (Out.nonzeroLocus _).isOpen.isClosed_compl
    have hmem : ∀ p : (PrimeSpectrum.zeroLocus (Set.range fun j => resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) :
        Set (PrimeSpectrum Γ(x.P.A.left, V))), hV.fromSpec p.1 ∈ W := by
      intro p j hj
      have hpV : hV.fromSpec p.1 ∈ V := by
        have : hV.fromSpec p.1 ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
        rwa [hV.range_fromSpec] at this
      have h₁ := (GlobalTheory.AmpleSpan.isUnit_gs_iff (𝟙 _) _ _ (h hpV) _).1
        ((GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (s (Fin.castLE hk j)) (𝟙 _) (hV.fromSpec p.1) (k := c) (h hpV)).1 hj)
      have h₂ : hV.fromSpec p.1 ∈ x.P.A.left.basicOpen (resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) := by
        have := x.P.A.left.basicOpen_res (show Γ(x.P.A.left, x.P.L.U c) from (s (Fin.castLE hk j)).f c) (homOfLE h).op
        exact this.ge ⟨hpV, h₁⟩
      have h₃ : p.1 ∈ hV.fromSpec ⁻¹ᵁ x.P.A.left.basicOpen (resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) := h₂
      rw [hV.fromSpec_preimage_basicOpen] at h₃
      exact h₃ (p.2 ⟨j, rfl⟩)
    have hind : Topology.IsInducing fun p : (PrimeSpectrum.zeroLocus
        (Set.range fun j => resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) :
        Set (PrimeSpectrum Γ(x.P.A.left, V))) => hV.fromSpec p.1 :=
      hV.fromSpec.isOpenEmbedding.isInducing.comp Topology.IsInducing.subtypeVal
    refine (hind.codRestrict hmem).topologicalKrullDim_le.trans ?_
    obtain ⟨p, hp⟩ := hne
    refine GlobalTheory.T.topologicalKrullDim_le_of_finite_common_zeros hL K x n (x.P.g - k) (fun j => s ⟨k + j, by have := j.2; omega⟩) W hn hW
      ⟨_, hmem ⟨p, hp⟩⟩ (Set.Finite.subset hZ ?_)
    rintro y ⟨hy₁, hy₂⟩ i
    by_cases hi : i.val < k
    · exact hy₁ ⟨i, hi⟩
    · have := hy₂ ⟨i - k, by have := i.2; omega⟩
      simp only [show k + (i.val - k) = i.val by omega] at this
      exact this

end GlobalTheory.KeyKa
end

