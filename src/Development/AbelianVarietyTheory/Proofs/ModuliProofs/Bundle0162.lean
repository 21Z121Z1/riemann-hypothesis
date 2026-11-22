import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0158
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0157
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenRelNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelFiniteOverModuliModelDescends
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0149
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeRingKrullDimThetaFamilyGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.GenericDim

open GlobalTheory.CoordChart

theorem exists_secCoord_field {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {σ : Type} (th : σ → M.Sec)
    {K : Type} [Field K] (x : Sp K ⟶ X) : ∃ v, SecCoord M th x v := by
  let p₀ : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have h : x p₀ ∈ ⨆ i, M.U i := by rw [hM.cover]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  refine GlobalTheory.SegreCoord.exists_secCoord hM (k := k) fun y => ?_
  have : y = p₀ := Subsingleton.elim (α := PrimeSpectrum K) _ _
  rw [this]; exact hk

theorem exists_common_field {R L : Type} [CommRing R] [CommRing L] [IsDomain L] (q : Ideal R) [q.IsPrime]
    (φ : R →+* L) (h : RingHom.ker φ = q) :
    ∃ (K : Type) (_ : Field K) (lam : L →+* K) (j : FractionRing (R ⧸ q) →+* K), Function.Injective lam ∧
      j.comp ((algebraMap (R ⧸ q) _).comp (Ideal.Quotient.mk q)) = lam.comp φ := by
  have hl := IsFractionRing.injective L (FractionRing L)
  have hχ : Function.Injective ((algebraMap L (FractionRing L)).comp (Ideal.Quotient.lift q φ fun a ha => h.ge ha)) :=
    hl.comp ((Ideal.injective_lift_iff fun a ha => h.ge ha).2 h)
  refine ⟨FractionRing L, inferInstance, algebraMap L (FractionRing L),
    IsFractionRing.lift (A := R ⧸ q) (K := FractionRing (R ⧸ q)) hχ, hl, ?_⟩
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, IsFractionRing.lift_algebraMap hχ, RingHom.comp_apply,
    RingHom.comp_apply]
  exact congrArg _ (Ideal.Quotient.lift_mk q φ _)

theorem exists_extension {o : Type} [CommRing o] {g n N' : ℕ} {I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)}
    (Y : MMPre n N' I) {R : Type} [CommRing R] (β : o →+* R) (x : Sp R ⟶ Y.MM) [IsOpenImmersion x]
    (hx : x ≫ Y.s = spMap β) (q : Ideal R) [q.IsPrime] (hmin : q ∈ minimalPrimes R)
    (y : R →+* FractionRing (R ⧸ q)) (hy : y = (algebraMap (R ⧸ q) _).comp (Ideal.Quotient.mk q))
    (v : Ix g (N' ^ 2) → FractionRing (R ⧸ q)) (hv : SecCoord Y.de Y.th (spMap y ≫ x) v)
    (P : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (hP : P.IsPrime) (hI : I ≤ P)
    (hle : P ≤ RingHom.ker (MvPolynomial.eval₂Hom (y.comp β) v)) :
    ∃ (K : Type) (_ : Field K) (j : FractionRing (R ⧸ q) →+* K) (u : Kˣ),
      RingHom.ker (MvPolynomial.eval₂Hom (j.comp (y.comp β)) (fun a => u * j (v a))) = P := by
  have h3 : (spMap y ≫ x) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hx, sp_comp]
  have hK := Y.loc _ _ _ _ h3 hv
  set ev := MvPolynomial.eval₂Hom (y.comp β) v with hev
  let e : (MvPolynomial (Ix g (N' ^ 2)) o ⧸ P) →+* FractionRing (R ⧸ q) :=
    Ideal.Quotient.lift P ev fun a ha => hle ha
  haveI : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  let L := Localization.AtPrime (RingHom.ker e)
  have hu : ∀ s : (RingHom.ker e).primeCompl, IsUnit (e s) := fun s => IsUnit.mk0 _ s.2
  let ψ : L →+* FractionRing (R ⧸ q) := IsLocalization.lift (M := (RingHom.ker e).primeCompl) hu
  let π : MvPolynomial (Ix g (N' ^ 2)) o →+* L := (algebraMap _ L).comp (Ideal.Quotient.mk P)
  have hπ : ∀ F, ψ (π F) = ev F := fun F => by
    simp only [ψ, π, RingHom.comp_apply, IsLocalization.lift_eq]
    rfl
  have hπe : ∀ F, MvPolynomial.eval₂ (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a)) F = π F := fun F => by
    conv_rhs => rw [← MvPolynomial.eval₂_eta F, MvPolynomial.eval₂_comp_left]
    rfl
  have hπ0 : ∀ F, π F = 0 ↔ F ∈ P := fun F => by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff _ (IsLocalization.injective L (RingHom.ker e).primeCompl_le_nonZeroDivisors)
  have hψ : ∀ l, ψ l ≠ 0 → IsUnit l := by
    intro l hl
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker e).primeCompl l
    rw [IsLocalization.AtPrime.isUnit_mk'_iff L (RingHom.ker e)]
    intro ha
    apply hl
    change ψ (IsLocalization.mk' L a s) = 0
    rw [IsLocalization.lift_mk'_spec, mul_zero]
    exact ha
  have hw : ∀ a, ψ (π (MvPolynomial.X a)) = v a := fun a => by rw [hπ]; simp [hev]
  have hβ : ψ.comp (π.comp MvPolynomial.C) = y.comp β := by ext t; simp [hπ, hev]
  have hL : InMM n N' I (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a)) := by
    refine ⟨fun F hF => by rw [hπe, hπ0]; exact hI hF, fun r hr a => ?_⟩
    obtain ⟨c, hc⟩ := hK.2 ⊥ Ideal.isPrime_bot a
    refine ⟨c, fun hm => hr.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (hψ _ ?_))⟩
    rw [hw]
    simpa using hc
  obtain ⟨z, ⟨hz1, hz2⟩, -⟩ := Y.pts L _ _ hL
  have h4 := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hz2).1 _ ψ
  have h5 : (spMap ψ ≫ z) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hz1, sp_comp, hβ]
  have heq : spMap ψ ≫ z = spMap y ≫ x := by
    refine (Y.pts _ _ _ hK).unique ⟨h5, ?_⟩ ⟨h3, hv⟩
    simpa only [hw] using h4
  have hr : Set.range z ⊆ Set.range x := by
    rintro _ ⟨p, rfl⟩
    let p₀ : Sp (FractionRing (R ⧸ q)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing (R ⧸ q)))
    have hs : p ⤳ spMap ψ p₀ := by
      refine (PrimeSpectrum.le_iff_specializes (R := L) p (spMap ψ p₀)).1 ?_
      intro l hl
      change ψ l ∈ (⊥ : Ideal _)
      by_contra hne
      exact p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hl (hψ _ (by simpa using hne)))
    refine (hs.map z.continuous).mem_open x.isOpenEmbedding.isOpen_range ⟨spMap y p₀, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, heq]
  obtain ⟨φ, hφ⟩ := sp_surj (IsOpenImmersion.lift x z hr)
  have hz : spMap φ ≫ x = z := by rw [hφ, IsOpenImmersion.lift_fac]
  have hφy : ψ.comp φ = y := sp_inj (by rw [← cancel_mono x, ← sp_comp, Category.assoc, hz, heq])
  have hφβ : φ.comp β = π.comp MvPolynomial.C := sp_inj (by rw [← sp_comp, ← hx, ← Category.assoc, hz, hz1])
  have hy0 : ∀ r, y r = 0 ↔ r ∈ q := fun r => by
    rw [hy, RingHom.comp_apply, map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ q) _),
      Ideal.Quotient.eq_zero_iff_mem]
  have hk1 : RingHom.ker φ ≤ q := fun r hr => by
    rw [RingHom.mem_ker] at hr
    rw [← hy0, ← hφy, RingHom.comp_apply, hr, map_zero]
  have hk2 : q ≤ RingHom.ker φ := hmin.2 ⟨RingHom.ker_isPrime φ, bot_le⟩ hk1
  haveI : IsDomain L := IsLocalization.isDomain_localization (RingHom.ker e).primeCompl_le_nonZeroDivisors
  obtain ⟨K, _, lam, j, hl, hj⟩ := exists_common_field q φ (le_antisymm hk1 hk2)
  rw [← hy] at hj
  have h6 := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hv).1 _ j
  have h7 := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hz2).1 _ lam
  rw [← Category.assoc, sp_comp, hj, ← sp_comp, Category.assoc, hz] at h6
  obtain ⟨u, hu'⟩ := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB h6).2.2 _ h7
  refine ⟨K, inferInstance, j, u, ?_⟩
  ext F
  rw [RingHom.mem_ker, ← hπ0, ← map_eq_zero_iff lam hl, ← hπe, MvPolynomial.eval₂_comp_left, ← RingHom.comp_assoc, hj,
    RingHom.comp_assoc, hφβ, MvPolynomial.coe_eval₂Hom, ← funext hu']
  rfl

theorem le_ringKrullDim_of_independent {o : Type} [CommRing o] [IsDomain o] {R : Type} [CommRing R] [Algebra o R]
    [Algebra.FiniteType o R] {d : ℕ}
    (h : ∀ (q : Ideal R) [q.IsPrime], q ∈ minimalPrimes R → ∃ y : Fin d → FractionRing (R ⧸ q), AlgebraicIndependent o y)
    (q : Ideal (FractionRing o ⊗[o] R)) (hq : q ∈ minimalPrimes (FractionRing o ⊗[o] R)) :
    (d : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q) := by
  have hqp : q.IsPrime := hq.1.1
  let f : R →ₐ[o] FractionRing o ⊗[o] R := Algebra.TensorProduct.includeRight
  have hmin : q.comap f ∈ minimalPrimes R := by
    letI : Algebra R (FractionRing o ⊗[o] R) := Algebra.TensorProduct.rightAlgebra
    have h1 := IsLocalization.minimalPrimes_map (Algebra.algebraMapSubmonoid R (nonZeroDivisors o))
      (FractionRing o ⊗[o] R) ⊥
    rw [Ideal.map_bot] at h1
    have h2 : q ∈ (⊥ : Ideal (FractionRing o ⊗[o] R)).minimalPrimes := hq
    rw [h1] at h2
    exact h2
  obtain ⟨y, hy⟩ := h (q.comap f) hmin
  let B := (FractionRing o ⊗[o] R) ⧸ q
  let f' : (R ⧸ q.comap f) →ₐ[o] FractionRing B :=
    (IsScalarTower.toAlgHom o B (FractionRing B)).comp (Ideal.quotientMapₐ q f le_rfl)
  have hf' : Function.Injective f' :=
    (IsFractionRing.injective B (FractionRing B)).comp (Ideal.quotientMap_injective' (f := f.toRingHom) (H := le_rfl) le_rfl)
  let j : FractionRing (R ⧸ q.comap f) →ₐ[o] FractionRing B := IsFractionRing.liftAlgHom hf'
  have h1 : AlgebraicIndependent o (j ∘ y) := hy.map' j.toRingHom.injective
  have : Algebra.IsAlgebraic o (FractionRing o) := IsLocalization.isAlgebraic _ (nonZeroDivisors o)
  have h2 := (h1.extendScalars (FractionRing o)).cardinalMk_le_trdeg
  have : Algebra.IsAlgebraic B (FractionRing B) := IsLocalization.isAlgebraic _ (nonZeroDivisors B)
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq (FractionRing o) B
  have : FaithfulSMul (FractionRing o) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap (FractionRing o) B).injective
  rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top (FractionRing o) B (FractionRing B), hs2] at h2
  have h3 : d ≤ s := by simpa using h2
  rw [hs1]
  exact_mod_cast h3

theorem le_ringKrullDim_genericFibre : Out.Laws → Out.Laws2 → ∀ (g n N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ) (F : WFam n em C Mat κ), 3 ≤ N' → Odd N' → ArBase em → GoodClass em C Mat κ w w' d → ∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ F.U.toScheme), IsOpenImmersion x → x ≫ F.U.ι ≫ F.Y.s = spMap (algebraMap o R) → ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R), (d : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q) := by
  intro h1 h2 g n N' J Mat κ w w' o _ b em C d F hN _ hb hC R _ _ x hox hx
  have : IsDedekindDomain o := hb.1
  have hx' : (x ≫ F.U.ι) ≫ F.Y.s = spMap (algebraMap o R) := by rw [Category.assoc, hx]
  have : Algebra.FiniteType o R := by
    obtain ⟨N, i, hi, -, hs⟩ := F.Y.qproj
    have := isProper_str o N
    have h : LocallyOfFiniteType (spMap (algebraMap o R)) := by
      rw [← hx', ← hs]; infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
    exact RingHom.finiteType_algebraMap.mp h
  refine le_ringKrullDim_of_independent fun q _ hq => ?_
  let y : R →+* FractionRing (R ⧸ q) := (algebraMap (R ⧸ q) _).comp (Ideal.Quotient.mk q)
  have hy : y.comp (algebraMap o R) = algebraMap o _ := by
    rw [IsScalarTower.algebraMap_eq o (R ⧸ q) (FractionRing (R ⧸ q))]; rfl
  obtain ⟨v, hv⟩ := exists_secCoord_field F.Y.isLB F.Y.th (spMap y ≫ x ≫ F.U.ι)
  have hK := F.Y.loc _ (y.comp (algebraMap o R)) _ _ (by rw [Category.assoc, hx', sp_comp]) hv
  obtain ⟨c, hc⟩ := hK.2 ⊥ Ideal.isPrime_bot 0
  obtain ⟨P, a₀, a, hP, hI, hle, -, hind⟩ := GlobalTheory.T.theta_ideal_prime_avoiding_variable h1 h2 g N' J Mat κ w w' o b em C d hb hC
    (RingHom.ker (MvPolynomial.eval₂Hom (y.comp (algebraMap o R)) v)) _ (by omega) (RingHom.ker_isPrime _)
    (fun G hG => hK.1 G hG) (by rw [RingHom.mem_ker, MvPolynomial.eval₂Hom_X']; simpa using hc)
  obtain ⟨K, _, j, u, hker⟩ := exists_extension F.Y _ (x ≫ F.U.ι) hx' q hq y rfl v hv P hP hI hle
  refine ⟨fun i => v (a i) / v a₀, algebraicIndependent_iff.2 fun G hG => hind K _ _ hker G ?_⟩
  have := congrArg j hG
  rw [map_zero, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, ← hy] at this
  convert this using 2
  ext i
  simp [mul_div_mul_left]

end GlobalTheory.ZM.GenericDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaCoordinateSchemeDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_thetaCoordinateSchemeData : ∀ (o : Type) [CommRing o] [IsDedekindDomain o] (g n N' : ℕ) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)), 0 < N' → I.IsRadical → (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → (∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ I → F ∈ I) → Nonempty (MMPre n N' I) := by
  first | exact @GlobalTheory.ZM.nonempty_MMPre | exact GlobalTheory.ZM.nonempty_MMPre | (intros; apply GlobalTheory.ZM.nonempty_MMPre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisedIsoCommutesFieldAutomorphismOfTorsion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.SerreTwist

theorem iso_eq_of_torsion (hL : Laws) {C : Type} [Field C] [IsAlgClosed C] (Q Q' : PolAV (Sp C))
    (a b : Q.A ≅ Q'.A) (ha : η[Q.A] ≫ a.hom = η[Q'.A]) (hb : η[Q.A] ≫ b.hom = η[Q'.A])
    (la : LBIso Q.L (Q'.L.pull a.hom.left)) (lb : LBIso Q.L (Q'.L.pull b.hom.left))
    {k : ℕ} (hk : 3 ≤ k) (hkC : (k : C) ≠ 0)
    (h : ∀ x : 𝟙_ (Over (Sp C)) ⟶ Q.A, x ^ k = 1 → x ≫ a.hom = x ≫ b.hom) : a.hom = b.hom := by
  have hη : η[Q.A] ≫ (a ≪≫ b.symm).hom = η[Q.A] := by
    rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, ha, ← hb, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hmon : IsMonHom (a ≪≫ b.symm).hom := hL.rigidity _ Q.A Q.A Q.isAb Q.isAb _ hη
  have hpb : LBIso (Q.L.pull (a ≪≫ b.symm).hom.left) (Q'.L.pull a.hom.left) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso lb _
      (by rw [← Over.comp_left, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  obtain ⟨w, hw⟩ : LBIso Q.L (Q.L.pull (a ≪≫ b.symm).hom.left) :=
    LBIso.trans Q.isLB (pull_isLB Q'.isLB _) (pull_isLB Q.isLB _) la (LBIso.symm hpb)
  have hfix : ∀ x : Over.mk (𝟙 (Sp C)) ⟶ Q.A, x ^ k = 1 → x ≫ (a ≪≫ b.symm).hom = x := by
    intro x hx
    rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, h x hx, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have key := GlobalTheory.MatchRigid.aut_eq_id hL Q (𝟙 (Sp C)) hk hkC (a ≪≫ b.symm) w hw hfix
  have := congrArg (· ≫ b.hom) key
  simpa using this

theorem exists_fibre (hB : PolBaseChangeSt) {S S' : Scheme.{0}} (P : PolAV S) (t : S' ⟶ S) :
    ∃ (Q : PolAV S') (e : Q.A.left ≅ (Over.mk t ⊗ P.A).left),
      e.hom ≫ (fst (Over.mk t) P.A).left = Q.A.hom ∧
      LBIso Q.L (P.L.pull (e.hom ≫ (snd (Over.mk t) P.A).left)) ∧
      ∃ F : (𝟙_ (Over S') ⟶ Q.A) →* (Over.mk t ⟶ P.A),
        ∀ x, x.left ≫ e.hom = (lift (𝟙 (Over.mk t)) (F x)).left := by
  obtain ⟨Q, g, hg, -, hmul, w, hw⟩ := hB S S' t P
  have hpb : IsPullback Q.A.hom g t P.A.hom := hg.flip
  let c : Over.mk t ⟶ Over.mk ((𝟙_ (Over S')).hom ≫ t) := Over.homMk (𝟙 S') (by simp)
  have hsnd : hpb.isoPullback.hom ≫ (snd (Over.mk t) P.A).left = g := by
    rw [Over.snd_left]; exact hpb.isoPullback_hom_snd
  refine ⟨Q, hpb.isoPullback, ?_, ?_,
    MonoidHom.mk' (fun x => c ≫ toBase hg.w x) (fun x y => by simp only [hmul, MonObj.comp_mul]), fun x => ?_⟩
  · rw [Over.fst_left]; exact hpb.isoPullback_hom_fst
  · rw [hsnd]; exact LBIso.symm ⟨w, hw⟩
  · apply pullback.hom_ext
    · simp [c]
      exact (pullback.lift_fst _ _ _).symm
    · have hs : hpb.isoPullback.hom ≫ pullback.snd (Over.mk t).hom P.A.hom = g := hpb.isoPullback_hom_snd
      rw [Category.assoc, hs, Over.lift_left]
      erw [pullback.lift_snd]
      simp [c, toBase]

theorem prod_iso_eq (hL : Laws) {S : Scheme.{0}} (P P' : PolAV S) {C : Type} [Field C] [IsAlgClosed C]
    (t : Sp C ⟶ S) {k : ℕ} (hk : 3 ≤ k) (hkC : (k : C) ≠ 0) (φ : Fin 2 → (Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P'.A))
    (h1 : ∀ i, (φ i).hom ≫ fst _ _ = fst _ _)
    (h2 : ∀ i, lift (𝟙 (Over.mk t)) (1 : Over.mk t ⟶ P.A) ≫ (φ i).hom ≫ snd _ _ = 1)
    (h3 : ∀ i, LBIso (P.L.pull (snd (Over.mk t) P.A).left) (P'.L.pull ((φ i).hom ≫ snd (Over.mk t) P'.A).left))
    (h4 : ∀ x : Over.mk t ⟶ P.A, x ^ k = 1 →
      lift (𝟙 (Over.mk t)) x ≫ (φ 0).hom ≫ snd _ _ = lift (𝟙 (Over.mk t)) x ≫ (φ 1).hom ≫ snd _ _) :
    (φ 0).hom = (φ 1).hom := by
  obtain ⟨Q, e, he1, he2, F, hF⟩ := exists_fibre hL.polBaseChange P t
  obtain ⟨Q', e', he1', he2', F', hF'⟩ := exists_fibre hL.polBaseChange P' t

  have hlift : ∀ i (z : Over.mk t ⟶ P.A), lift (𝟙 (Over.mk t)) z ≫ (φ i).hom =
      lift (𝟙 (Over.mk t)) (lift (𝟙 (Over.mk t)) z ≫ (φ i).hom ≫ snd _ _) := by
    intro i z
    apply CartesianMonoidalCategory.hom_ext
    · simp [h1 i]
    · simp
  have h1' : ∀ i, (φ i).hom.left ≫ (fst (Over.mk t) P'.A).left = (fst (Over.mk t) P.A).left := by
    intro i
    rw [← Over.comp_left, h1 i]

  let θ : Fin 2 → (Q.A.left ≅ Q'.A.left) := fun i => e ≪≫ (Over.forget S).mapIso (φ i) ≪≫ e'.symm
  have hθ : ∀ i, (θ i).hom = e.hom ≫ (φ i).hom.left ≫ e'.inv := fun i => rfl
  have hw : ∀ i, (θ i).hom ≫ Q'.A.hom = Q.A.hom := by
    intro i
    rw [hθ, ← he1', ← he1, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, h1']
  let a : Fin 2 → (Q.A ≅ Q'.A) := fun i => Over.isoMk (θ i) (hw i)
  have ha_left : ∀ i, (a i).hom.left = e.hom ≫ (φ i).hom.left ≫ e'.inv := fun i => rfl
  have hcomp : ∀ i (x : 𝟙_ (Over (Sp C)) ⟶ Q.A), x.left ≫ (a i).hom.left =
      (lift (𝟙 (Over.mk t)) (lift (𝟙 (Over.mk t)) (F x) ≫ (φ i).hom ≫ snd _ _)).left ≫ e'.inv := by
    intro i x
    rw [ha_left, ← Category.assoc, hF, ← Category.assoc, ← Over.comp_left, hlift]

  have hone : ∀ (R : PolAV (Sp C)), (1 : 𝟙_ (Over (Sp C)) ⟶ R.A) = η[R.A] := by
    intro R
    rw [Hom.one_def, toUnit_unit, Category.id_comp]
  have ha : ∀ i, η[Q.A] ≫ (a i).hom = η[Q'.A] := by
    intro i
    apply Over.OverMorphism.ext
    rw [Over.comp_left, ← hone Q, hcomp, map_one, h2 i, ← map_one F', ← hF', hone Q', Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

  have la : ∀ i, LBIso Q.L (Q'.L.pull (a i).hom.left) := by
    intro i
    have h3e : LBIso (P.L.pull (e.hom ≫ (snd (Over.mk t) P.A).left))
        (P'.L.pull ((a i).hom.left ≫ e'.hom ≫ (snd (Over.mk t) P'.A).left)) :=
      GlobalTheory.GenSpread.lbIso_pull_comp e.hom rfl
        (by rw [ha_left, Over.comp_left]; simp only [Category.assoc, Iso.inv_hom_id_assoc]) (h3 i)
    have hQ' := GlobalTheory.GenSpread.lbIso_pull_of_lbIso he2' (a i).hom.left rfl
    exact LBIso.trans Q.isLB (pull_isLB P'.isLB _) (pull_isLB Q'.isLB _)
      (LBIso.trans Q.isLB (pull_isLB P.isLB _) (pull_isLB P'.isLB _) he2 h3e) (LBIso.symm hQ')

  have htor : ∀ x : 𝟙_ (Over (Sp C)) ⟶ Q.A, x ^ k = 1 → x ≫ (a 0).hom = x ≫ (a 1).hom := by
    intro x hx
    have hFx : F x ^ k = 1 := by rw [← map_pow, hx, map_one]
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, hcomp, hcomp, h4 (F x) hFx]
  have key := congrArg Over.Hom.left (iso_eq_of_torsion hL Q Q' (a 0) (a 1) (ha 0) (ha 1) (la 0) (la 1) hk hkC htor)
  rw [ha_left, ha_left] at key
  apply Over.OverMorphism.ext
  simpa using key

end GlobalTheory.SerreTwist

theorem GlobalTheory.SerreTwist.whisker_comp_eq : Laws → ∀ (S : Scheme.{0}) (P P' : PolAV S) (C : Type) [Field C] [IsAlgClosed C] (t : Sp C ⟶ S) (φ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P'.A), φ.hom ≫ fst _ _ = fst _ _ → lift (𝟙 (Over.mk t)) (1 : Over.mk t ⟶ P.A) ≫ φ.hom ≫ snd _ _ = 1 → LBIso (P.L.pull (snd (Over.mk t) P.A).left) (P'.L.pull (φ.hom ≫ snd (Over.mk t) P'.A).left) → ∀ k : ℕ, 3 ≤ k → (k : C) ≠ 0 → ∀ s : Over.mk t ≅ Over.mk t, (∀ x : Over.mk t ⟶ P.A, x ^ k = 1 → lift (𝟙 (Over.mk t)) (s.hom ≫ x) ≫ φ.hom ≫ snd _ _ = s.hom ≫ lift (𝟙 (Over.mk t)) x ≫ φ.hom ≫ snd _ _) → s.hom ▷ P.A ≫ φ.hom ≫ snd _ _ = φ.hom ≫ snd _ _ := by
  intro hL S P P' C inst1 inst2 t φ h1 h2 h3 k hk hkC s hs
  let ψ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P'.A := whiskerRightIso s P.A ≪≫ φ ≪≫ whiskerRightIso s.symm P'.A
  have hψ : ψ.hom = s.hom ▷ P.A ≫ φ.hom ≫ s.inv ▷ P'.A := rfl
  have hψs : ψ.hom ≫ snd _ _ = s.hom ▷ P.A ≫ φ.hom ≫ snd _ _ := by
    rw [hψ]; simp

  have hsw : ∀ z : Over.mk t ⟶ P.A,
      lift (𝟙 (Over.mk t)) z ≫ s.hom ▷ P.A = s.hom ≫ lift (𝟙 (Over.mk t)) (s.inv ≫ z) := by
    intro z
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have ψ1 : ψ.hom ≫ fst _ _ = fst _ _ := by
    rw [hψ]; simp [reassoc_of% h1]
  have ψ2 : lift (𝟙 (Over.mk t)) (1 : Over.mk t ⟶ P.A) ≫ ψ.hom ≫ snd _ _ = 1 := by
    rw [hψs, ← Category.assoc, hsw, MonObj.comp_one, Category.assoc, h2, MonObj.comp_one]
  have ψ3 : LBIso (P.L.pull (snd (Over.mk t) P.A).left) (P'.L.pull (ψ.hom ≫ snd (Over.mk t) P'.A).left) := by
    rw [hψs]
    exact GlobalTheory.GenSpread.lbIso_pull_comp (s.hom ▷ P.A).left (by rw [← Over.comp_left, whiskerRight_snd])
      (by rw [Over.comp_left]) h3
  have ψ4 : ∀ x : Over.mk t ⟶ P.A, x ^ k = 1 →
      lift (𝟙 (Over.mk t)) x ≫ φ.hom ≫ snd _ _ = lift (𝟙 (Over.mk t)) x ≫ ψ.hom ≫ snd _ _ := by
    intro x hx
    have hx' : (s.inv ≫ x) ^ k = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    conv_rhs => rw [hψs, ← Category.assoc, hsw, Category.assoc]
    rw [← hs _ hx', Iso.hom_inv_id_assoc]
  have key : φ.hom = ψ.hom :=
    GlobalTheory.SerreTwist.prod_iso_eq hL P P' t hk hkC ![φ, ψ] (Fin.forall_fin_two.2 ⟨h1, ψ1⟩)
      (Fin.forall_fin_two.2 ⟨h2, ψ2⟩) (Fin.forall_fin_two.2 ⟨h3, ψ3⟩) ψ4
  rw [← hψs, ← key]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RaisedModelLevelOneDescends
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.RaisedDescends

theorem map_nsmul_eq_pow {A Q : Type*} [AddMonoid A] [Group Q] (f : A → Q) (hf : ∀ a c, f (a + c) = f a * f c)
    (m : ℕ) (a : A) : f (m • a) = f a ^ m := by
  induction m with
  | zero =>
    have h := hf 0 0
    rw [add_zero] at h
    rw [zero_nsmul, pow_zero]
    exact left_eq_mul.mp h
  | succ m ih => rw [succ_nsmul, hf, ih, pow_succ]

theorem mono_spMap_of_isDedFrac {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) :
    Mono (spMap β) := by
  letI := β.toAlgebra
  have := h.2.2
  have : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (nonZeroDivisors O) (S := F)
  infer_instance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isDedFrac_of_isInc (l : Level H) (S A : ℕ) (hS : 0 < S) (hA : l.A = A) (h1 : A = 1) (β : RZ H S A →+* KA l)
    (hβ : IsInc (RZ H S A).subtype (KA l).val.toRingHom β) : IsDedFrac β := by
  subst hA
  exact (GlobalTheory.T.cmModelCoefficientSubring_dedekind_compatible_embedding E H l S 0 hS (by rw [h1, pow_zero])).2.2 β hβ

theorem Cpt_j_over {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F}
    (C : Cpt c t β) : C.j ≫ C.s = c ≫ spMap β := by
  rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]

theorem levComp_comp {D : Datum H} {l l' : Level H} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    {b : Base l B} {b' : Base l' B'} {b'' : Base l' B''} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}
    {s'' : S'' ⟶ Sp B''} {o'' : Obj D l' b'' s''} {o' : Obj D l' b' s'} {o : Obj D l b s} {r : S' ⟶ S} {g : S'' ⟶ S'}
    (m : ObjMap o'' o' g) {ν : SABMap o'.t o.t r} (h : LevComp o' o r ν) (ν' : SABMap o''.t o.t (g ≫ r))
    (e : ν'.φ = m.toSABMap.φ ≫ ν.φ) : LevComp o'' o (g ≫ r) ν' := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  · have h1 := h.1 a
    rw [← map_nsmul_eq_pow _ o'.eta_add] at h1
    rw [← map_nsmul_eq_pow _ o''.eta_add, e, ← Category.assoc, m.eta, Category.assoc, h1, Category.assoc]
  · have h1 := h.2 a
    rw [← map_nsmul_eq_pow _ o'.etaA_add] at h1
    rw [← map_nsmul_eq_pow _ o''.etaA_add, e, ← Category.assoc, m.etaA, Category.assoc, h1, Category.assoc]

theorem descends_of_raises : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ : Level H) (B : BaseModel T l₀) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), 0 < n → l₀.Dvd l → l.A = 1 → IsDedFrac β → Raises B Y → Y.Descends := by
  intro h1 h2 h3 E _ _ _ H D Xo n N T hN l₀ B l c O _ β Y hn hd hA hβ hR
  obtain ⟨b, r, ν, hb, hlev, ⟨a⟩⟩ := hR
  obtain ⟨k, r₁, ν₁, hr₁, hk, hlev₁, hfin, -⟩ := GlobalTheory.T.exists_finite_etale_surjective_levelMap E H D Xo hN l₀ l hd
  have hS : 0 < n * l₀.M := Nat.mul_pos hn (lt_of_lt_of_le (by norm_num) l₀.three_le)
  have hD₀ : IsDedFrac B.β := isDedFrac_of_isInc l₀ _ 1 hS B.A_one rfl _ B.β_inc
  have hD₁ : IsDedFrac (k.comp B.β) :=
    isDedFrac_of_isInc l _ 1 hS hA rfl _ fun x => (hk (B.β x)).trans (B.β_inc x)
  have hsm : Smooth (Xo l).s := by
    have := (Xo l).smooth
    exact SmoothOfRelativeDimension.smooth D.dim _
  obtain ⟨C', ⟨a'⟩⟩ := GlobalTheory.T.exists_normal_model_above_finite_cover E H _ _ _ _ _ B.β _ _ _ (Xo l).s (Xo l).univ.t (k.comp B.β) B.C (RingHom.id _) k r₁ hr₁ ν₁
    hD₀ hD₁ (RingHom.comp_id _)
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hsm).2.1 hfin
  have hbβ : β.comp b = (IntermediateField.inclusion c.le).toRingHom.comp (k.comp B.β) := by
    refine RingHom.ext fun x => Subtype.ext ?_
    exact (hb x).trans ((hk (B.β x)).trans (B.β_inc x)).symm
  have hred : IsReduced ((Xo l).XF c) :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ (pullback.snd _ _) inferInstance).1
  obtain ⟨ν₂, hν₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν₁ Y.m0.toSABMap
  have hover : r ≫ (Xo l₀).s = (pullback.fst _ _ ≫ r₁) ≫ (Xo l₀).s := by
    have := mono_spMap_of_isDedFrac hD₀
    rw [← cancel_mono (spMap B.β), Category.assoc, ← Cpt_j_over B.C, ← Category.assoc, ← a.j_comm, Category.assoc,
      a.π_over, ← Category.assoc, Cpt_j_over, Category.assoc, ← spMap_comp, hbβ, spMap_comp, spMap_comp,
      Category.assoc, Category.assoc, reassoc_of% hr₁, pullback.condition_assoc]
  obtain ⟨e₁, e₂⟩ := GlobalTheory.LevUniq.map_to_univ_unique h1 h2 h3 E H D l₀ l (Xo l₀) _ _ _ _ Y.oF r _ ν ν₂ hred hover hlev
    (levComp_comp Y.m0 hlev₁ ν₂ hν₂)
  obtain ⟨h, mu', hh, -, -, hj, hφ, hf⟩ := GlobalTheory.Models.Cpt.Above.exists_lift E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    B.C C' (ofModel Y) (RingHom.id _) b (IntermediateField.inclusion c.le).toRingHom r₁ ν₁ a' (pullback.fst _ _)
    Y.m0.toSABMap a.π a.mu a.π_over hβ hbβ pullback.condition
    (by rw [a.j_comm, e₁, Category.assoc]) (by rw [a.φ_comm, e₂, hν₂, Category.assoc])
  exact GlobalTheory.descends_of_above E H D l (Xo l) c O β Y _ (k.comp B.β) C' b ⟨h, hh, hf a.fin, mu', hj, hφ⟩ hD₁ hβ hbβ

end GlobalTheory.RaisedDescends

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReductionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_subset_abelianLocus_of_goodReduction : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (X : Scheme.{0}) (z : X ⟶ Sp ℤ) (G : Over X) [GrpObj G] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [Algebra V C] [IsFractionRing V C] (y : Sp V ⟶ X) (𝒜 : Over (Sp V)) [GrpObj 𝒜] (A : Over (Sp C)) [GrpObj A] (φ₁ : A.left ⟶ 𝒜.left) (φ₂ : A.left ⟶ G.left), LocallyOfFiniteType z → IsSemiAbelian G → IsAbelianScheme 𝒜 → IsGrpPullback A 𝒜 (spMap (algebraMap V C)) φ₁ → IsGrpPullback A G (spMap (algebraMap V C) ≫ y) φ₂ → Set.range y ⊆ abLocus G := by
  first | exact @GlobalTheory.range_subset_abLocus_of_goodReduction | exact GlobalTheory.range_subset_abLocus_of_goodReduction | (intros; apply GlobalTheory.range_subset_abLocus_of_goodReduction <;> assumption)
end

