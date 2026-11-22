import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingProdEqZeroOfLong
section
open GlobalTheory.LatJet
open scoped Classical

namespace GlobalTheory.LatJet.ProdZero

theorem b_mul_prod_eq_zero {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}
    (J : JetRing R I n) (l : List I) :
    ∀ ν : Idx I n, n + 1 < (∑ i, (ν : I → ℕ) i) + l.length →
      J.b ν * (l.map J.t).prod = 0 := by
  induction l with
  | nil =>
    intro ν h
    exact absurd ν.2 (by simpa using h)
  | cons a l ih =>
    intro ν h
    rw [List.map_cons, List.prod_cons, ← mul_assoc]
    have hm := J.mul ν ⟨Pi.single a 1, by
      rw [Finset.sum_pi_single']; simp⟩
    have ht : J.t a = J.b ⟨Pi.single a 1, by rw [Finset.sum_pi_single']; simp⟩ := rfl
    rw [ht, hm]
    by_cases hle : ∑ i, ((ν : I → ℕ) + (Pi.single a 1 : I → ℕ)) i ≤ n + 1
    · rw [dif_pos hle, smul_mul_assoc, ih _ ?_, smul_zero]
      have hs : ∑ i, ((ν : I → ℕ) + (Pi.single a 1 : I → ℕ)) i = (∑ i, (ν : I → ℕ) i) + 1 := by
        simp only [Pi.add_apply]
        rw [Finset.sum_add_distrib, Finset.sum_pi_single']
        simp
      show n + 1 < (∑ i, ((ν : I → ℕ) + (Pi.single a 1 : I → ℕ)) i) + l.length
      rw [hs]
      simp only [List.length_cons] at h
      omega
    · rw [dif_neg hle, zero_mul]

theorem prod_eq_zero {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}
    (J : JetRing R I n) (l : List I) (h : n + 1 < l.length) :
    (l.map J.t).prod = 0 := by
  have := b_mul_prod_eq_zero J l ⟨0, by simp⟩ (by simpa using h)
  rwa [J.one, one_mul] at this

end GlobalTheory.LatJet.ProdZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingReprMulPowerSeries
section
open GlobalTheory.LatJet
open scoped Classical

namespace GlobalTheory.JetMul

theorem finite_jet_index {I : Type} [Fintype I] {n : ℕ} : Finite (Idx I n) := by
  refine Finite.of_injective (fun ν : Idx I n => fun i => (⟨ν.1 i, ?_⟩ : Fin (n + 2))) ?_
  · have h1 : ν.1 i ≤ ∑ j, ν.1 j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 := ν.2
    omega
  · intro a b h
    apply Subtype.ext
    funext i
    have := congrFun h i
    simpa using congrArg Fin.val this

theorem reprMul {I : Type} [Fintype I] {n : ℕ} (J : JetRing ℂ I n) (F G : MvPowerSeries I ℂ) (x y : J.B)
    (hx : ∀ ν : Idx I n, J.b.repr x ν = ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) F)
    (hy : ∀ ν : Idx I n, J.b.repr y ν = ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) G)
    (μ : Idx I n) :
    J.b.repr (x * y) μ = ((∏ i, (μ.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm μ.1) (F * G) := by
  haveI : Finite (Idx I n) := finite_jet_index
  haveI : Fintype (Idx I n) := Fintype.ofFinite _
  have hb : ∀ ν ν' : Idx I n, J.b.repr (J.b ν * J.b ν') μ =
      if ν.1 + ν'.1 = μ.1 then ((∏ i, (ν.1 i + ν'.1 i).choose (ν.1 i) : ℕ) : ℂ) else 0 := by
    intro ν ν'
    rw [J.mul]
    split_ifs with h1 h2 h2
    · rw [map_nsmul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply, if_pos (Subtype.ext h2)]
      simp [nsmul_eq_mul]
    · rw [map_nsmul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply, if_neg (fun h => h2 (congrArg Subtype.val h))]
      simp
    · exact absurd (by rw [h2]; exact μ.2) h1
    · simp
  have hxy : x * y = ∑ ν, ∑ ν', (J.b.repr x ν * J.b.repr y ν') • (J.b ν * J.b ν') := by
    conv_lhs => rw [← J.b.sum_repr x, ← J.b.sum_repr y]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν' _ => ?_
    rw [smul_mul_smul_comm]
  rw [hxy, map_sum, Finsupp.finset_sum_apply]
  simp_rw [map_sum, Finsupp.finset_sum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, hb, hx, hy]
  have hfac : ∀ ν ν' : Idx I n, ν.1 + ν'.1 = μ.1 →
      (∏ i, (ν.1 i).factorial) * (∏ i, (ν'.1 i).factorial) * (∏ i, (ν.1 i + ν'.1 i).choose (ν.1 i)) =
        ∏ i, (μ.1 i).factorial := by
    intro ν ν' h
    rw [← h, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.add_apply, ← Nat.add_choose_mul_factorial_mul_factorial (ν.1 i) (ν'.1 i), Nat.choose_symm_add]
    ring
  have hterm : ∀ ν ν' : Idx I n,
      ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) F *
        (((∏ i, (ν'.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν'.1) G) *
        (if ν.1 + ν'.1 = μ.1 then ((∏ i, (ν.1 i + ν'.1 i).choose (ν.1 i) : ℕ) : ℂ) else 0) =
      if ν.1 + ν'.1 = μ.1 then ((∏ i, (μ.1 i).factorial : ℕ) : ℂ) *
        (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) F * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν'.1) G)
      else 0 := by
    intro ν ν'
    split_ifs with h
    · rw [← hfac ν ν' h]
      push_cast
      ring
    · simp
  simp_rw [hterm]
  rw [MvPowerSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_product' (f := fun ν ν' : Idx I n => if ν.1 + ν'.1 = μ.1 then ((∏ i, (μ.1 i).factorial : ℕ) : ℂ) *
        (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) F * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν'.1) G)
      else 0), ← Finset.sum_filter]
  have hle : ∀ p : (I →₀ ℕ) × (I →₀ ℕ), p ∈ Finset.HasAntidiagonal.antidiagonal (Finsupp.equivFunOnFinite.symm μ.1) →
      (∑ i, p.1 i ≤ n + 1) ∧ (∑ i, p.2 i ≤ n + 1) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hμ := μ.2
    have e : ∀ i, p.1 i + p.2 i = μ.1 i := fun i => by
      have := DFunLike.congr_fun hp i
      simpa using this
    have s : ∑ i, p.1 i + ∑ i, p.2 i = ∑ i, μ.1 i := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => e i
    omega
  refine Finset.sum_bij' (fun a _ => (Finsupp.equivFunOnFinite.symm a.1.1, Finsupp.equivFunOnFinite.symm a.2.1))
    (fun p hp => (⟨p.1, (hle p hp).1⟩, ⟨p.2, (hle p hp).2⟩)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    ext i
    simp [← ha.2]
  · intro p hp
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    funext i
    have := DFunLike.congr_fun hp i
    simpa using this
  · intro a ha
    rfl
  · intro p hp
    ext i <;> simp
  · intro a ha
    rw [Finset.mem_filter] at ha

end GlobalTheory.JetMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedPre
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.CxCoh.CxMap

universe u u'

variable {C : Type u} [Category.{0} C] {C' : Type u'} [Category.{0} C'] {K : Cx C} {K' : Cx C'}

def pre (m : CxMap K K') {G : C' ⥤ C} (θ : G ⟶ m.G) : CxMap K K' where
  G := G
  a0 T := (m.a0 T).comp (K.M0.map (θ.app T))
  a1 T := (m.a1 T).comp (K.M1.map (θ.app T))
  a2 T := (m.a2 T).comp (K.M2.map (θ.app T))
  a3 T := (m.a3 T).comp (K.M3.map (θ.app T))
  compDegreeZero_natural {T T'} φ x := by
    change m.a0 T' (K.M0.map (θ.app T') (K.M0.map (G.map φ) x)) =
      K'.M0.map φ (m.a0 T (K.M0.map (θ.app T) x))
    rw [← K.M0.map_comp, θ.naturality, K.M0.map_comp, m.compDegreeZero_natural]
  compDegreeOne_natural {T T'} φ x := by
    change m.a1 T' (K.M1.map (θ.app T') (K.M1.map (G.map φ) x)) =
      K'.M1.map φ (m.a1 T (K.M1.map (θ.app T) x))
    rw [← K.M1.map_comp, θ.naturality, K.M1.map_comp, m.compDegreeOne_natural]
  compDegreeTwo_natural {T T'} φ x := by
    change m.a2 T' (K.M2.map (θ.app T') (K.M2.map (G.map φ) x)) =
      K'.M2.map φ (m.a2 T (K.M2.map (θ.app T) x))
    rw [← K.M2.map_comp, θ.naturality, K.M2.map_comp, m.compDegreeTwo_natural]
  comp_commutes_diffZero T x := by
    change m.a1 T (K.M1.map (θ.app T) (K.d0 _ x)) = K'.d0 T (m.a0 T (K.M0.map (θ.app T) x))
    rw [← K.diffZero_natural, m.comp_commutes_diffZero]
  comp_commutes_diffOne T x := by
    change m.a2 T (K.M2.map (θ.app T) (K.d1 _ x)) = K'.d1 T (m.a1 T (K.M1.map (θ.app T) x))
    rw [← K.diffOne_natural, m.comp_commutes_diffOne]
  comp_commutes_diffTwo T x := by
    change m.a3 T (K.M3.map (θ.app T) (K.d2 _ x)) = K'.d2 T (m.a2 T (K.M2.map (θ.app T) x))
    rw [← K.diffTwo_natural, m.comp_commutes_diffTwo]

theorem joined_pre (m : CxMap K K') {G : C' ⥤ C} (θ : G ⟶ m.G) : (m.pre θ).Joined m θ :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

end GlobalTheory.CxCoh.CxMap

namespace GlobalTheory.PDForm

def pairB {D D' : Data} (Λ' : Lift D') {σ : D.R →+* D'.R} (φ : D'.X ⟶ D.X) {φ₀ : D'.X₀ ⟶ D.X₀}
    (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) : CxMap (KK D.κ D.t) ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)) :=
  (morMap m).comp ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L))

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAlongIdIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

noncomputable section
namespace GlobalTheory.PrincSubring

def powLB {S : Scheme.{0}} (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) : LB (Out.powObj A 8).left :=
  LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (Out.powPr A uv.1) (Out.powPr A uv.2)).left)
    fun uv => GlobalTheory.W8 uv.1 uv.2

def KerAlong {S : Scheme.{0}} (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) {S' : Scheme.{0}} (g : S' ⟶ S) : Prop :=
  ∀ (T : Over S) (a : T.left ⟶ S'), a ≫ g = T.hom → ∀ x : T ⟶ A, IsTrivial (slice A P x) → x = 1

theorem KerAlong.comp {S S' S'' : Scheme.{0}} {A : Over S} [GrpObj A] {P : LB (A ⊗ A).left} {g : S' ⟶ S}
    (h : KerAlong A P g) (f : S'' ⟶ S') : KerAlong A P (f ≫ g) :=
  fun T a ha => h T (a ≫ f) ((Category.assoc _ _ _).trans ha)

end GlobalTheory.PrincSubring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelPolarisationTrivialLiftsSqZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.KTrivSqZero

theorem exists_specializes_of_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] {π : R →+* R₀}
    (hπ : Function.Surjective π) (hJ : RingHom.ker π ≤ Ideal.jacobson ⊥) (p : PrimeSpectrum R) :
    ∃ q : PrimeSpectrum R₀, p ⤳ PrimeSpectrum.comap π q := by
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.2.ne_top
  have hJm : RingHom.ker π ≤ m := hJ.trans (sInf_le ⟨bot_le, hm⟩)
  have : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [range_comap_of_surjective _ _ hπ]
    exact hJm
  obtain ⟨q, hq⟩ := this
  refine ⟨q, ?_⟩
  rw [hq, ← PrimeSpectrum.le_iff_specializes]
  exact hpm

theorem le_jacobson_of_sq_eq_bot {R : Type} [CommRing R] {J : Ideal R} (h : J ^ 2 = ⊥) : J ≤ Ideal.jacobson ⊥ := by
  intro x hx
  have hx2 : x ∈ (⊥ : Ideal R).radical := ⟨2, by
    have : x ^ 2 ∈ J ^ 2 := Ideal.pow_mem_pow hx 2
    rw [h] at this
    exact this⟩
  exact Ideal.radical_le_jacobson hx2

theorem kTriv_lift : ∀ (R R₀ : Type) [CommRing R] [IsNoetherianRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀] (Y : Over (Sp R)) [GrpObj Y] (i : Y₀.left ⟶ Y.left), IsAbelianScheme Y → IsGrpPullback Y₀ Y (spMap π) i → ∀ (L₀ : LB Y₀.left) (L : LB Y.left), L₀.IsLB → L.IsLB → RelAmple Y L → LBIso L₀ (L.pull i) → KTriv Y₀ L₀ → KTriv Y L := by
  intro R R₀ _ _ _ π hπ hsq Y₀ _ Y _ i hY hi L₀ L hL₀ hL hA e hK
  have hJ := le_jacobson_of_sq_eq_bot hsq
  have key : ∀ p : Sp R, ∃ U : (Sp R).Opens, p ∈ U ∧
      KTriv ((Over.pullback U.ι).obj Y) (L.pull (pullback.fst Y.hom U.ι)) := fun p => by
    obtain ⟨q, hq⟩ := exists_specializes_of_surjective hπ hJ p
    obtain ⟨U, hU, H⟩ := GlobalTheory.KTrivGlob.exists_open hL hL₀ hY hA hi e hK q
    exact ⟨U, hq.mem_open U.2 hU, H⟩
  choose U hU hK using key
  have hL' := fun p => pull_isLB hL (pullback.fst Y.hom (U p).ι)
  exact GlobalTheory.CoverGlue.kTriv_of_cover _ _ U Y _ _
    (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hU p⟩)
    (fun p => isGrpPullback_pullback Y (U p).ι) _ _ hL hL' (fun p => GlobalTheory.lbIso_refl (hL' p)) hY
    (fun p => GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hY (isGrpPullback_pullback Y (U p).ι)) hK

end GlobalTheory.KTrivSqZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelStableIffPulledBackIdentity
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.TrStab

theorem one_left' {S : Scheme.{0}} (G : Over S) [GrpObj G] (T : Over S) : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.toUnit_left']

theorem eq_one_of_push {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {θ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f θ) {T : Over S'} (x : T ⟶ G')
    (hx : x.left ≫ θ = T.hom ≫ f ≫ η[G].left) : x = 1 := by
  ext
  apply h.1.hom_ext
  · rw [hx, one_left', Category.assoc, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h]
  · rw [Over.w x, Over.w (1 : T ⟶ G')]

theorem push_one {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {θ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f θ) (T : Over S') :
    (1 : T ⟶ G').left ≫ θ = T.hom ≫ f ≫ η[G].left := by
  rw [one_left', Category.assoc, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h]

end GlobalTheory.UPel.HT.ES.TrStab

namespace GlobalTheory.UPel.HT.ES

open TrStab

theorem kerStableAt_iff_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁ : o₁.A ⟶ B₁) (ψ : o.A ⟶ B), IsGrpPullback B₁ B t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → (KerStableAt o ψ t ↔ KerStableAt o₁ ψ₁ (𝟙 T)) := by
  intro p _ D R _ b N T Y s₁ s t o₁ o m B₁ _ _ B _ _ θ ψ₁ ψ hB hψ
  constructor
  · intro h T' σ hσ g hg a
    rw [Category.comp_id] at hσ
    subst hσ
    have hG : pushPt m.cart.1.w g ≫ ψ = 1 := by
      ext
      rw [one_left', Over.comp_left]
      show (g.left ≫ m.φ) ≫ ψ.left = _
      rw [Category.assoc, hψ, ← Category.assoc, ← Over.comp_left, hg, push_one hB]
      rfl
    have h2 := h (Over.mk (T'.hom ≫ t)) T'.hom rfl (pushPt m.cart.1.w g) hG a
    apply eq_one_of_push hB
    have e := congrArg Over.Hom.left h2
    rw [one_left', Over.comp_left, Over.comp_left] at e
    simp only [Over.comp_left, Category.assoc]
    rw [← hψ, ← Category.assoc (o₁.act.act a).left, m.act a, Category.assoc]
    exact e
  · intro h T0 σ hσ g hg a
    have w : g.left ≫ o.A.hom = σ ≫ t := by rw [Over.w g, hσ]
    let g₁ : Over.mk σ ⟶ o₁.A := Over.homMk (m.cart.1.lift g.left σ w) (m.cart.1.lift_snd _ _ _)
    have hg₁ : g₁.left ≫ m.φ = g.left := m.cart.1.lift_fst _ _ _
    have h1 : g₁ ≫ ψ₁ = 1 := by
      apply eq_one_of_push hB
      rw [Over.comp_left, Category.assoc, ← hψ, ← Category.assoc, hg₁, ← Over.comp_left, hg, one_left', ← hσ, Category.assoc]
      rfl
    have h2 := h (Over.mk σ) σ (Category.comp_id σ) g₁ h1 a
    ext
    rw [one_left', Over.comp_left, Over.comp_left, ← hg₁, Category.assoc, ← Category.assoc m.φ (o.act.act a).left,
      ← m.act a]
    simp only [Category.assoc]
    rw [hψ]
    have e : (g₁ ≫ o₁.act.act a ≫ ψ₁).left ≫ θ = (1 : Over.mk σ ⟶ B₁).left ≫ θ := by rw [h2]
    rw [push_one hB] at e
    simp only [Over.comp_left, Category.assoc] at e
    rw [e, ← hσ, Category.assoc]
    rfl

end GlobalTheory.UPel.HT.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumFibreOfComposableBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem spMap_comp' {A B K : Type} [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K) :
    spMap (h.comp f) = spMap h ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem eSec_hom' {S : Scheme.{0}} (G : Over S) [GrpObj G] : eSec G ≫ G.hom = 𝟙 _ := by
  simpa [eSec] using Over.w η[G]

theorem gs_appLE' {X Y Z : Scheme.{0}} (φ : Y ⟶ X) (r : Z ⟶ Y) (p : Z) (U : X.Opens) (V : Y.Opens) (e : V ≤ φ ⁻¹ᵁ U)
    (hp : r p ∈ V) (a : Γ(X, U)) : gs r p V ((φ.appLE U V e).hom a) = gs (r ≫ φ) p U a := by
  rw [← gs_pull r φ p U (e hp) a, ← gs_res r p e hp]
  rfl

theorem dualMap_alg {B K : Type} [CommRing B] [CommRing K] (h : B →+* K) (a : B) :
    GlobalTheory.MBLow.dualMap h (algebraMap B _ a) = algebraMap K _ (h a) := by
  ext <;> simp [GlobalTheory.MBLow.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_eps {B K : Type} [CommRing B] [CommRing K] (h : B →+* K) :
    GlobalTheory.MBLow.dualMap h DualNumber.eps = DualNumber.eps := by
  ext <;> simp [GlobalTheory.MBLow.dualMap]

theorem dual_decomp {A : Type} [CommRing A] (z : DualNumber A) :
    z = algebraMap A _ z.fst + algebraMap A _ z.snd * DualNumber.eps := by
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem ringHom_dual_ext {A K : Type} [CommRing A] [CommRing K] (F G : DualNumber A →+* K)
    (h1 : ∀ a, F (algebraMap A _ a) = G (algebraMap A _ a)) (h2 : F DualNumber.eps = G DualNumber.eps) : F = G := by
  refine DFunLike.ext _ _ fun z => ?_
  rw [dual_decomp z, map_add, map_add, map_mul, map_mul, h1, h1, h2]

end GlobalTheory.KeyEven

namespace GlobalTheory.KeyEven

theorem keyPB_of_keyOn_comp : ∀ (A B K : Type) [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K)
    (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (g : ℕ) (y : Fin g → (epsR A ⟶ G))
    (x : KeyIn B) (x' : KeyIn K) (hg : x.P.g = g) (hg' : x'.P.g = g),
    KeyOn f x G L σ (fun i => y (i.cast hg)) → KeyOn (h.comp f) x' G L σ (fun i => y (i.cast hg')) → KeyPB x' x h := by
  intro A B K _ _ _ f h G _ _ L σ g y x x' hg hg' H H'
  obtain ⟨φ, he, ψ, F, hpb, hψ, hrig, hsec, hF1, hF2, hv⟩ := H
  obtain ⟨φ', he', ψ', F', hpb', hψ', hrig', hsec', hF1', hF2', hv'⟩ := H'
  have hc : spMap (h.comp f) = spMap h ≫ spMap f := spMap_comp' f h
  obtain ⟨φ₁, h1, h2⟩ : ∃ φ₁ : x'.P.A.left ⟶ x.P.A.left, φ₁ ≫ φ = φ' ∧ φ₁ ≫ x.P.A.hom = x'.P.A.hom ≫ spMap h :=
    ⟨hpb.1.lift φ' (x'.P.A.hom ≫ spMap h) (by rw [hpb'.1.w, hc, Category.assoc]), hpb.1.lift_fst _ _ _,
      hpb.1.lift_snd _ _ _⟩
  subst h1
  have gp : IsGrpPullback x'.P.A x.P.A (spMap h) φ₁ := IsGrpPullback.cancel hpb (hpb'.congr hc rfl) h2
  have he₁ : eSec x'.P.A ≫ φ₁ = spMap h ≫ eSec x.P.A := by
    apply hpb.1.hom_ext
    · rw [Category.assoc, he', Category.assoc, he, hc, Category.assoc]
    · rw [Category.assoc, h2, ← Category.assoc, eSec_hom', Category.assoc, eSec_hom']
      rfl
  have hL := L.isLB
  have hx := x.P.isLB
  have hx' := x'.P.isLB
  have pψ := (isGen_iff ψ).1 hψ
  have pψ' := (isGen_iff ψ').1 hψ'
  obtain ⟨w, T⟩ := exists_cancel hL ψ ψ' pψ pψ' hx hx'
  have hg₁ : x'.P.g = x.P.g := hg'.trans hg.symm
  refine ⟨φ₁, he₁, w, hg₁, GlobalTheory.MBLow.dualMap h, gp, (isGen_iff w).2 (T.pgen_cancel hL pψ pψ'), ?_, ?_,
    dualMap_alg h, dualMap_eps h, ?_⟩
  ·
    have H := (maps_iff ψ _ (fun _ => eSec G) _ x.rig L.rig (spMap f) _ (rigPull_le φ (spMap f) he L.L)
      (fun _ => rfl)).1 hrig
    have H'' := (maps_iff ψ' _ (fun _ => eSec G) _ x'.rig L.rig (spMap (h.comp f)) _
      (rigPull_le (φ₁ ≫ φ) (spMap (h.comp f)) he' L.L) (fun _ => rfl)).1 hrig'
    rw [hc] at H''
    exact (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap h) _ (rigPull_le φ₁ (spMap h) he₁ x.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel hL (fun _ => he₁) H H'')
  ·
    intro j i hle
    apply fn_ext
    intro p hp
    obtain ⟨c, hcp⟩ := exists_chart hL (φ (φ₁ p))
    have hk : φ₁ p ∈ x.P.L.U (j PUnit.unit) := hle hp
    have le₀ : (L.L.pull φ).U (fun _ => c) ⊓ x.P.L.U (j PUnit.unit) ≤ φ ⁻¹ᵁ L.L.U c := fun q hq => mem_pull.1 hq.1
    have m₀ : φ₁ p ∈ (L.L.pull φ).U (fun _ => c) ⊓ x.P.L.U (j PUnit.unit) := ⟨mem_pull.2 hcp, hk⟩
    have e₀ := congrArg (gs φ₁ p _) (hsec (fun _ => c) (j PUnit.unit) le₀)
    dsimp only at e₀
    rw [gs_appLE' φ φ₁ p _ _ le₀ m₀] at e₀
    erw [gs_mul φ₁ p _ m₀] at e₀
    erw [gs_unit φ₁ p _ m₀, gs_res φ₁ p _ m₀] at e₀
    have le₁ : ((L.L.pull (φ₁ ≫ φ)).U (fun _ => c)) ⊓ x'.P.L.U i ≤ (φ₁ ≫ φ) ⁻¹ᵁ L.L.U c :=
      fun q hq => mem_pull.1 hq.1
    have m₁ : (𝟙 x'.P.A.left) p ∈ (L.L.pull (φ₁ ≫ φ)).U (fun _ => c) ⊓ x'.P.L.U i := ⟨mem_pull.2 hcp, hp.2⟩
    have e₁ := congrArg (gs (𝟙 _) p _) (hsec' (fun _ => c) i le₁)
    dsimp only at e₁
    rw [gs_appLE' (φ₁ ≫ φ) (𝟙 _) p _ _ le₁ m₁] at e₁
    erw [gs_mul (𝟙 _) p _ m₁] at e₁
    erw [gs_unit (𝟙 _) p _ m₁, gs_res (𝟙 _) p _ m₁] at e₁
    rw [Category.id_comp] at e₁
    have tri := T (x'.P.A.left) (𝟙 _) p c (j PUnit.unit) i hcp hk hp.2
    rw [gs_appLE' φ₁ (𝟙 _) p _ _ hle hp, Category.id_comp]
    erw [gs_mul (𝟙 _) p _ hp]
    erw [gs_unit (𝟙 _) p _ hp, gs_res (𝟙 _) p _ hp]
    change gs φ₁ p _ _ = (gw w (𝟙 _) p (j PUnit.unit) i).val * _
    have e₂ : (gw ψ' (𝟙 _) p c i).val * gs (𝟙 _) p (x'.P.L.U i) (x'.th.f i) =
        (gw ψ φ₁ p c (j PUnit.unit)).val * gs φ₁ p (x.P.L.U (j PUnit.unit)) (x.th.f (j PUnit.unit)) :=
      e₁.symm.trans e₀
    rw [tri, Category.id_comp, Units.val_mul, _root_.mul_assoc] at e₂
    exact ((Units.mul_right_inj _).1 e₂).symm
  ·
    intro i
    apply hpb.1.hom_ext
    · have a1 := hv (i.cast hg₁)
      have a2 := hv' i
      simp only at a1 a2
      rw [Category.assoc, a2, Category.assoc, a1, Fin.cast_cast, ← Category.assoc, ← spMap_comp']
      congr 2
      refine ringHom_dual_ext _ _ (fun a => ?_) ?_
      · simp only [RingHom.comp_apply, hF1, hF1', dualMap_alg]
      · simp only [RingHom.comp_apply, hF2, hF2', dualMap_eps]
    · rw [Category.assoc, h2, ← Category.assoc, Over.w (x'.v i), Category.assoc, Over.w (x.v _)]
      show spMap (algebraMap K (DualNumber K)) ≫ spMap h = spMap (GlobalTheory.MBLow.dualMap h) ≫ spMap (algebraMap B (DualNumber B))
      rw [← spMap_comp', ← spMap_comp']
      congr 1
      exact RingHom.ext fun a => (dualMap_alg h a).symm

end GlobalTheory.KeyEven
end

