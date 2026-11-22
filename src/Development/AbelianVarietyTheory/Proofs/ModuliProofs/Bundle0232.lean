import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0230
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0197
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0231
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0171
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0164
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0172
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0158
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0073
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientOfOpenCoverReducedBase

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelSchemeUniversalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeKernel_scheme_universal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), admitted l 𝔓 p → ∃ (Hk : Scheme.{0}) (π₁ : Hk ⟶ Xo.X) (o₁ : Ob D l (π₁ ≫ Xo.s)) (m₁ : ObjMap o₁ Xo.univ π₁) (K : Set o₁.t.G.left), IsFinite π₁ ∧ Etale π₁ ∧ HeckeSet D o₁.t 𝔓 p i K ∧ EtSet o₁.t.G K ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (z : Sp k ⟶ Hk) (z' : Sp k ⟶ Hk), z ≫ π₁ = z' ≫ π₁ → (∀ (u : Over.mk z ⟶ o₁.t.G) (u' : Over.mk z' ⟶ o₁.t.G), u.left ≫ m₁.toSABMap.φ = u'.left ≫ m₁.toSABMap.φ → (Set.range u.left ⊆ K ↔ Set.range u'.left ⊆ K)) → z = z') ∧ ∀ (T : Scheme.{0}) (s : T ⟶ Sp (KA l)) (o : Ob D l s) (f : T ⟶ Xo.X) (mu : ObjMap o Xo.univ f) (τ : Fin (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) → (𝟙_ (Over T) ⟶ o.t.G)) (K' : Set o.t.G.left), Lists (p ^ 2) τ K' → HeckeSet D o.t 𝔓 p i K' → ∃ (h : T ⟶ Hk) (n : ObjMap o o₁ h), h ≫ π₁ = f ∧ n.toSABMap.φ ≫ m₁.toSABMap.φ = mu.toSABMap.φ ∧ K' = n.toSABMap.φ ⁻¹' K := by
  first | exact @GlobalTheory.HkFam.exists_heckeKernelScheme | exact GlobalTheory.HkFam.exists_heckeKernelScheme | (intros; apply GlobalTheory.HkFam.exists_heckeKernelScheme <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliPrimePowerFullLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.FullLevel

theorem finiteDimensional_KA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    FiniteDimensional ℚ (KA l) := by
  have hA := l.A_pos
  refine IntermediateField.finiteDimensional_adjoin ?_
  intro x hx
  rcases hx with rfl | hx
  · have h2 : H.rt0 ^ 2 = algebraMap ℚ ℂ (-(H.d : ℚ)) := by
      rw [H.sqrt_neg_disc_sq]; simp
    have hi : IsIntegral ℚ (H.rt0 ^ 2) := by rw [h2]; exact isIntegral_algebraMap
    exact IsIntegral.of_pow two_pos hi
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    have hz : IsPrimitiveRoot (zeta l.A) l.A := by
      unfold zeta; exact Complex.isPrimitiveRoot_exp l.A hA.ne'
    refine IsIntegral.of_pow hA ?_
    rw [hz.pow_eq_one]; exact isIntegral_one

private theorem constPt_comp' {k : Type} [Field k] {X Y : Scheme.{0}} (x : Sp (DualNumber k) ⟶ X)
    (f : X ⟶ Y) : constPt (x ≫ f) = constPt x ≫ f := by
  simp only [constPt, Category.assoc]

theorem moduli_of_family (hL : Out.Laws) (hL2 : Out.Laws2)
    (hth : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {g : ℕ} {J : Type} (a : J → 𝓞 E)
    (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (hbas : IsSympBasis D bas) (hw : a w = H.w0)
    (hw' : a w' = H.bar H.w0) (hgen : Subring.closure (Set.range a) = ⊤) (l : Level H) (hMA : l.M ∣ l.A)
    {o : Type} [CommRing o] [IsDomain o] [Algebra o (KA l)] [hfr : IsFractionRing o (KA l)] (b : TBase o l.A) (ρ : o)
    (hρ : algebraMap o (KA l) ρ = (baseKA l).ρ) (hζ : algebraMap o (KA l) (b.ζ : o) = (baseKA l).ζ)
    {U : Scheme.{0}} (sU : U ⟶ Sp o) (tU : TObj g l.A J b sU) (τU : SAB H U) (hq : IsQProjOver sU)
    (hτ : IsPEL D a bas ρ tU τU)
    (hdim : ∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ U), IsOpenImmersion x →
      x ≫ sU = spMap (algebraMap o R) → ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R),
        (D.dim : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q))
    (hinj : ∀ (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ U) (s' : Sp R ⟶ Sp o) (t : TObj g l.A J b s'),
      x ≫ sU = y ≫ sU → TMap t tU x → TMap t tU y → x = y)
    (hrep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g l.A J b s') (τ : SAB H S), IsReduced S →
      IsPEL D a bas ρ t τ → (∀ (K : Type) [Field K], (Sp K ⟶ S) → CharZero K) →
      ∃! f : S ⟶ U, f ≫ sU = s' ∧ TMap t tU f) :
    Nonempty (Moduli D l) := by
  classical
  obtain ⟨X, p, sX, sq⟩ : ∃ (X : Scheme.{0}) (p : X ⟶ U) (sX : X ⟶ Sp (KA l)),
      IsPullback p sX sU (spMap (algebraMap o (KA l))) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  have hqX : IsQProjOver sX := isQProjOver_of_isPullback_spMap _ sq hq
  have hlft : LocallyOfFiniteType sX := lft_of_qproj hqX
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : FiniteDimensional ℚ (KA l) := finiteDimensional_KA l
  haveI : Algebra.IsAlgebraic ℚ (KA l) := Algebra.IsAlgebraic.of_finite ℚ (KA l)
  obtain ⟨tX, htX⟩ := tObj_pull o g l.A J b U X sU (sX ≫ spMap (algebraMap o (KA l))) p tU sq.w
  obtain ⟨τX, hτX⟩ := exists_isPEL_of_tmap E H D g J a bas l.A o b ρ U X sU
    (sX ≫ spMap (algebraMap o (KA l))) tU tX τU p sq.w htX hτ
  obtain ⟨ob, hob⟩ := ThetaToObj.exists_obj_under hL hL2 E H D g J a bas l o b ρ X sX tX τX hMA hbas hfr hρ hζ
    (Or.inr inferInstance) hτX
  have hsep : ∀ (R : Type) [CommRing R] [IsLocalRing R] (x1 x2 : Sp R ⟶ X) (s' : Sp R ⟶ Sp o)
      (t' : TObj g l.A J b s'), TMap t' tX x1 → TMap t' tX x2 → x1 ≫ sX = x2 ≫ sX → x1 = x2 := by
    intro R _ _ x1 x2 s' t' h1 h2 hs
    refine sq.hom_ext ?_ hs
    refine hinj R _ _ s' t' ?_ (TMap.comp h1 htX) (TMap.comp h2 htX)
    rw [Category.assoc, Category.assoc, sq.w, ← Category.assoc, hs, Category.assoc]
  refine ⟨{ X := X, s := sX, qproj := hqX, smooth := ?_, univ := ob, rep := ?_, unram := ?_ }⟩
  · refine smoothOfRelativeDimension_of_dim_of_directions_le (KA l) X sX D.dim hlft ?_ ?_
    · intro R _ _ x hx _ q hq'
      haveI : IsOpenImmersion (x ≫ sq.isoPullback.hom) := inferInstance
      exact dim_generic_chart sU _ hdim R (x ≫ sq.isoPullback.hom) q hq'
    · intro K' _ _ r β x hxs hdir
      have hρsq : ρ ^ 2 = -(H.d : o) := by
        apply IsFractionRing.injective o (KA l)
        rw [map_pow, hρ, (baseKA l).ρ_sq]; simp
      have hb : x ≫ sX ≫ spMap (algebraMap o (KA l)) =
          spMap ((algebraMap K' (TrivSqZeroExt K' (Fin r → K'))).comp (β.comp (algebraMap o (KA l)))) := by
        rw [← Category.assoc, hxs, ← spMap_comp]
      obtain ⟨t1, ht1⟩ := tObj_pull o g l.A J b X _ (sX ≫ spMap (algebraMap o (KA l))) _ x tX hb
      obtain ⟨τ1, hτ1⟩ := exists_isPEL_of_tmap E H D g J a bas l.A o b ρ X _
        (sX ≫ spMap (algebraMap o (KA l))) _ tX t1 τX x hb ht1 hτX
      haveI : CharZero K' := charZero_of_hom (spMap β)
      refine T.tangent_le_dim_alt hL hL2 hth E H D g J a w w' bas l.A o b ρ K' r (β.comp (algebraMap o (KA l))) t1 τ1
        hw hw' hρsq hτ1 ?_
      intro lam t' h1 h2
      apply hdir lam
      rw [constPt_comp']
      refine hsep (DualNumber K') _ _ _ t' (TMap.comp h1 ht1) (TMap.comp h2 ht1) ?_
      simpa only [constPt_comp'] using eq_constPt ((spMap (dirMap lam) ≫ x) ≫ sX)
  · intro S s' hS o'
    obtain ⟨t', ht'u, ht'p⟩ := ObjTheta.exists_tObj hL hL2 E H D g J a bas l (KA l) o (baseKA l) b ρ
      (algebraMap o (KA l)) S s' o' hbas hρ hζ
    have hch : ∀ (K : Type) [Field K], (Sp K ⟶ S) → CharZero K := fun K _ y => charZero_of_hom (y ≫ s')
    obtain ⟨f, ⟨hf1, hf2⟩, hfu⟩ := hrep S (s' ≫ spMap (algebraMap o (KA l))) t' o'.t hS ht'p hch
    have hiff := fun (f' : S ⟶ X) => UnderMap.objMap_iff_tMap hL hL2 E H D g J a bas l (KA l) o (baseKA l) b X S
      sX s' (sX ≫ spMap (algebraMap o (KA l))) (s' ≫ spMap (algebraMap o (KA l))) ob o' tX t' f' hMA hgen hob ht'u
    refine ⟨sq.lift f s' hf1, ⟨sq.lift_snd _ _ _, (hiff _).mpr (TMap.cancel htX (by rw [sq.lift_fst]; exact hf2))⟩, ?_⟩
    rintro f2 ⟨hf2s, hm⟩
    have htm : TMap t' tX f2 := (hiff f2).mp hm
    apply sq.hom_ext
    · rw [sq.lift_fst]
      apply hfu
      refine ⟨?_, TMap.comp htm htX⟩
      rw [Category.assoc, sq.w, ← Category.assoc, hf2s]
    · rw [sq.lift_snd, hf2s]
  · intro k _ x o' hm1 hm2
    obtain ⟨t', ht'u, -⟩ := ObjTheta.exists_tObj hL hL2 E H D g J a bas l (KA l) o (baseKA l) b ρ
      (algebraMap o (KA l)) _ (x ≫ sX) o' hbas hρ hζ
    have hiff := fun (f' : Sp (DualNumber k) ⟶ X) => UnderMap.objMap_iff_tMap hL hL2 E H D g J a bas l (KA l) o
      (baseKA l) b X _ sX (x ≫ sX) (sX ≫ spMap (algebraMap o (KA l))) ((x ≫ sX) ≫ spMap (algebraMap o (KA l)))
      ob o' tX t' f' hMA hgen hob ht'u
    refine hsep (DualNumber k) x (constPt x) _ t' ((hiff x).mp hm1) ((hiff _).mp hm2) ?_
    simpa only [constPt_comp'] using eq_constPt (x ≫ sX)

theorem exists_generating_family {E : Type} [Field E] [NumberField E] (u u' : 𝓞 E) :
    ∃ (J : Type) (_ : Finite J) (a : J → 𝓞 E) (w w' : J), a w = u ∧ a w' = u' ∧ Subring.closure (Set.range a) = ⊤ := by
  classical
  let bs := NumberField.RingOfIntegers.basis E
  refine ⟨Option (Option (Module.Free.ChooseBasisIndex ℤ (𝓞 E))), inferInstance,
    fun i => Option.elim i u (fun i' => Option.elim i' u' (fun k => bs k)), none, some none, rfl, rfl, ?_⟩
  rw [eq_top_iff]
  intro x hx0
  clear hx0
  have hx : x ∈ Submodule.span ℤ (Set.range bs) := by rw [bs.span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact Subring.subset_closure ⟨some (some k), rfl⟩
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul n y _ hy => exact zsmul_mem hy n

end GlobalTheory.ZM.FullLevel

open GlobalTheory.ZM.FullLevel in

theorem GlobalTheory.ZM.exists_moduli_prime_power_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n : ℕ), 1 ≤ D.p + D.q → n.Prime → Odd n → ∃ j : ℕ, ∀ l : Level H, l.M = n → l.A = (n ^ j) ^ 2 → Nonempty (Moduli D l) := by
  intro hL hL2 hth hU E _ _ _ H D n hpq hn hodd
  obtain ⟨bas, hbas⟩ := ZM.exists_isSympBasis E H D
  obtain ⟨J, hJ, a, w, w', hw, hw', hgen⟩ := exists_generating_family (E := E) H.w0 (H.bar H.w0)
  obtain ⟨Mat, κ, hGood⟩ := T.isGoodThetaComplexClass_unitaryFullLevel hL hL2 hth hU E H D _ J a w w' bas hpq hbas hw hw' hgen
  obtain ⟨j₁, hj₁⟩ := hGood n hn hodd
  obtain ⟨j₂, hj₂⟩ := T.nonempty_thetaFamily_over_open_closure hL hL2 _ J Mat κ n w w' hn hodd
  obtain ⟨j₃, hj₃⟩ := T.existsUnique_map_to_thetaFamily_openPart hL hL2 _ J Mat κ n w w' hn hodd
  refine ⟨max (max j₁ j₂) (max j₃ 1), ?_⟩
  intro l hM hA
  have hj1 : j₁ ≤ max (max j₁ j₂) (max j₃ 1) := le_max_of_le_left (le_max_left _ _)
  have hj2 : j₂ ≤ max (max j₁ j₂) (max j₃ 1) := le_max_of_le_left (le_max_right _ _)
  have hj3 : j₃ ≤ max (max j₁ j₂) (max j₃ 1) := le_max_of_le_right (le_max_left _ _)
  have hj0 : 1 ≤ max (max j₁ j₂) (max j₃ 1) := le_max_of_le_right (le_max_right _ _)
  generalize max (max j₁ j₂) (max j₃ 1) = j at hj1 hj2 hj3 hj0 hA
  obtain ⟨o, _, b, em, ρ, _, har, hfr, hem, hρ, hζ⟩ := IntegersAway.exists_tBase_fractionRing E H l
  cases l
  dsimp only at hA hM
  subst hA
  have hM' := hM.symm
  subst hM'
  haveI := har.1
  have hemρ : em ρ = H.rt0 := by rw [← hem, hρ]; rfl
  have h3n : 3 ≤ n := by
    have h2 := hn.two_le
    have hne : n ≠ 2 := by
      rintro rfl
      exact (Nat.not_odd_iff_even.mpr even_two) hodd
    omega
  have hN3 : 3 ≤ n ^ j := le_trans h3n (Nat.le_self_pow (by omega) n)
  have hoddN : Odd (n ^ j) := hodd.pow
  have hGd := hj₁ j hj1 (n ^ j) rfl o b em ρ hemρ
  obtain ⟨F⟩ := hj₂ j hj2 o b em _ D.dim har hGd
  obtain ⟨hqU, -, hredU, hinjU⟩ := T.thetaClosureOpenFamily_qproj_flat_reduced_ext hL hL2 o _ n (n ^ j) J b em _ Mat κ F hoddN
  have hqU' : IsQProjOver (F.U.ι ≫ F.Y.s) := hqU.resolve_right (not_not.mpr inferInstance)
  haveI := hredU
  haveI := lft_of_qproj hqU'
  haveI : IsLocallyNoetherian F.U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (F.U.ι ≫ F.Y.s)
  obtain ⟨τU, hτU⟩ := T.exists_isPELTriple_of_dense_fibres hL hL2 hth E H D _ J a bas w w' hpq hbas hw hw' hgen _ o b em ρ F.U.toScheme
    (F.U.ι ≫ F.Y.s) F.univ hemρ har.2.2 F.dense
  refine moduli_of_family hL hL2 hth D a w w' bas hbas hw hw' hgen _
    (dvd_pow (dvd_pow_self n (by omega)) two_ne_zero) b ρ hρ hζ (F.U.ι ≫ F.Y.s) F.univ τU hqU' hτU
    (T.le_ringKrullDim_thetaFamily_genericFibre hL hL2 _ n (n ^ j) J Mat κ w w' o b em _ D.dim F hN3 hoddN har hGd) hinjU ?_
  intro S s' t τ hS hP hch
  refine hj₃ j hj3 o b em _ D.dim har hGd F S s' t hS ?_ ?_
  · refine Dense.mono ?_ dense_univ
    intro p _
    haveI := hch _ (S.fromSpecResidueField p)
    exact ⟨_, inferInstance, S.fromSpecResidueField p,
      ⟨IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply p _⟩,
      T.pelObject_fibre_from_complex_charZero hL hL2 E H D _ J a w w' bas hpq hbas hw hw' hgen (n ^ j) o b em ρ hemρ har S s' t τ hP _ _⟩
  · intro K _ _ x t' hT
    haveI := hch K x
    obtain ⟨K₀, _, β, i, e, t₀, tx, tc, -, -, htx, htx0, htc0, hC⟩ :=
      T.pelObject_fibre_from_complex_charZero hL hL2 E H D _ J a w w' bas hpq hbas hw hw' hgen (n ^ j) o b em ρ hemρ har S s' t τ hP K x
    have s1 := (hGd.shape tc hC).1
    have s2 := ((shape_prim_pull_and_descend o _ _ J b Mat κ w w' _ _ _ _ _ t₀ tc htc0).2.2 K₀ rfl
      inferInstance inferInstance).1 s1
    have s3 := (shape_prim_pull_and_descend o _ _ J b Mat κ w w' _ _ _ _ _ t₀ tx htx0).1 s2
    have htt : TMap t' tx (𝟙 _) := TMap.cancel htx (by rw [Category.id_comp]; exact hT)
    exact (shape_prim_pull_and_descend o _ _ J b Mat κ w w' _ _ _ _ _ tx t' htt).1 s3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelFamilyLocalisationPrimePowerLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SiegelFromSharp

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _

def restrictBase {h k : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} (j : B →+* B') (hj : j ζ = ζ')
    {S : Scheme.{0}} {s' : S ⟶ Sp B'} (c : SiegPre h k ζ' s') : SiegPre h k ζ (s' ≫ spMap j) where
  A := c.A
  ab := c.ab
  P := c.P
  isLB := c.isLB
  rig₁ := c.rig₁
  rig₂ := c.rig₂
  symm := c.symm
  lev := c.lev
  lev_add := c.lev_add
  lev_tors := c.lev_tors
  geom := by
    intro K _ _ x β z hx hz
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ s')
    refine c.geom K x φ.hom z hφ.symm ?_
    have : spMap (φ.hom.comp j) = spMap β := by
      rw [← spMap_comp, ← hx, ← Category.assoc, ← hφ]; rfl
    have e : φ.hom.comp j = β := congrArg CommRingCat.Hom.hom (Spec.map_injective this)
    rw [hz, ← e, ← hj]; rfl

theorem finiteType_of_isQProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsQProjOver f) :
    QuasiCompact f ∧ LocallyOfFiniteType f := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have := isProper_str R N
  exact ⟨inferInstance, inferInstance⟩

theorem dirMap_base {o K : Type} [CommRing o] [Field K] {r : ℕ} (β : o →+* K) (lam : (Fin r → K) →ₗ[K] K) :
    spMap (dirMap lam) ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) =
      constPt (spMap (dirMap lam)) ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) := by
  simp only [constPt, Category.assoc, spMap_comp]
  congr 1
  ext x <;> simp [dirMap]

theorem constPt_comp {K : Type} [Field K] {X Y : Scheme.{0}} (x : Sp (DualNumber K) ⟶ X) (f : X ⟶ Y) :
    constPt x ≫ f = constPt (x ≫ f) := by
  simp only [constPt, Category.assoc]

theorem nonempty_siegelFamily (L1 : Out.Laws) (L2 : Out.Laws2)
    (L3 : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
    {h g p n N' : ℕ} (hh : 1 ≤ h) (hp : p.Prime) {W : Matrix (Fin 8) (Fin 8) ℤ} {J : Type} [Finite J]
    {a : J → Matrix (Fin 8) (Fin 8) ℤ} {w w' : J}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} (hW : IsE8 W) (hbas : IsSharpBasis W bas)
    (hw : (W + W.transpose) * a w = W) (hw' : (W + W.transpose) * a w' = W.transpose)
    (hu : ∀ u v, ∃ j, a j = Matrix.single u v 1) {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ}
    (h3 : 3 ≤ N') (hodd : Odd N') {o : Type} [CommRing o] {b : TBase o (N' ^ 2)} {em : o →+* ℂ}
    (j : o →+* ZP p (N' ^ 2)) (har : ArBase em) (hj : j (b.ζ : o) = zetaZP p (N' ^ 2))
    (hconst : ∀ (K : Type) [Field K] (y : Sp (DualNumber K) ⟶ Sp (ZP p (N' ^ 2))), y = constPt y)
    (good : GoodClass em (SharpClass (b := b) W a bas em) Mat κ w w' (h * (h + 1) / 2))
    (F : WFam n em (SharpClass (b := b) W a bas em) Mat κ)
    (rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s'), IsReduced S →
      Dense (fromSet em (SharpClass (b := b) W a bas em) t) → t.FibShape Mat κ →
      ∃! f : S ⟶ F.U.toScheme, f ≫ F.U.ι ≫ F.Y.s = s' ∧ TMap t F.univ f) :
    Nonempty (SiegelFamily h p (N' ^ 2)) := by
  have hk : Odd (N' ^ 2) := hodd.pow
  have hk3 : 3 ≤ N' ^ 2 := by nlinarith
  have hζ : b.ζ ^ N' ^ 2 = 1 := by
    refine Units.ext (har.2.2 ?_)
    rw [Units.val_pow_eq_pow_val, map_pow, (b.prim ℂ em).pow_eq_one, Units.val_one, map_one]
  haveI : IsDedekindDomain o := har.1
  haveI : CharZero o := RingHom.charZero em
  obtain ⟨hq, hflat, hred, htan⟩ := GlobalTheory.T.thetaClosureOpenFamily_qproj_flat_reduced_ext L1 L2 o g n N' J b em _ Mat κ F hodd
  obtain ⟨hqc, hft⟩ := finiteType_of_isQProjOver (hq.resolve_right (not_not.2 inferInstance))
  haveI : IsLocallyNoetherian F.U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (F.U.ι ≫ F.Y.s)
  obtain ⟨c, hc, hsharp⟩ := GlobalTheory.T.exists_eighthPower_principalSiegel_of_dense L1 L2 L3 h g W J a bas hW hbas hu _ o b em _ _ F.univ hk F.dense

  have pull : ∀ (S : Scheme.{0}) (s : S ⟶ Sp o) (c' : SiegPre h (N' ^ 2) (b.ζ : o) s) (t : TObj g (N' ^ 2) J b s)
      (f : S ⟶ F.U.toScheme), c'.Principal → IsSharp W a bas t c' → (SiegPB c' c f ↔ TMap t F.univ f) := by
    intro S s c' t f h1 h2
    have := GlobalTheory.T.siegelPullback_iff_eighthPower_pullback L1 L2 h g W J a bas hW hbas _ o b _ _ _ _ c c' F.univ t f hc h1 hsharp h2
    exact ⟨this.1, this.2 hu⟩
  have hsm : SmoothOfRelativeDimension (h * (h + 1) / 2) (F.U.ι ≫ F.Y.s) := by
    refine GlobalTheory.T.smoothOfRelativeDimension_of_flat_dedekind_tangent_le o _ _ _ har.2.1 hflat hft
      (GlobalTheory.T.le_ringKrullDim_thetaFamily_genericFibre L1 L2 g n N' J Mat κ w w' o b em _ _ F h3 hodd har good) ?_
    intro K _ _ r β x hx hlam
    obtain ⟨p1, p2, -⟩ := GlobalTheory.T.siegelPre_pullback_principal_ringChange h (N' ^ 2) o o (b.ζ : o) (b.ζ : o) (RingHom.id o) _ _ _
      (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β)) x rfl (by rw [spMap_id, Category.comp_id, hx])
    obtain ⟨c', hc'⟩ := p1 c
    have hp' := p2 c c' hc' hc
    obtain ⟨t', ht'⟩ := GlobalTheory.T.exists_thetaObject_eighthPower_principalSiegel L1 L2 h g W J a bas hW hbas _ o b _ _ c' hk hk3 hζ hp'
    have hm : TMap t' F.univ x := (pull _ _ c' t' x hp' ht').1 hc'
    refine GlobalTheory.T.siegelFamily_tangent_dimension_bound L1 L2 L3 h g W J a bas hW hbas w w' hw hw' _ o b K r β t' c' hp' ht' ?_
    intro lam t'' m1 m2
    refine hlam lam ?_
    rw [← constPt_comp]
    refine htan (DualNumber K) _ _ _ t'' ?_ (((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ F.univ t' t'').2 x _ hm).1 m1)
      (((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ F.univ t' t'').2 x _ hm).1 m2)
    rw [Category.assoc, Category.assoc, hx]
    exact dirMap_base β lam
  obtain ⟨q1, q2, -⟩ := GlobalTheory.T.siegelPre_pullback_principal_ringChange h (N' ^ 2) o _ (b.ζ : o) _ j _ _ (F.U.ι ≫ F.Y.s)
    (pullback.snd (F.U.ι ≫ F.Y.s) (spMap j)) (pullback.fst _ _) hj pullback.condition
  obtain ⟨u, hupb⟩ := q1 c
  have hup := q2 c u hupb hc
  refine ⟨⟨pullback (F.U.ι ≫ F.Y.s) (spMap j), pullback.snd _ _,
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hsm, inferInstance, u, hup, ?_, ?_⟩⟩
  · intro C O _ _ _ _ _ _ _ _ hO hpC β c₁ hgen hamp
    have hp₁ : c₁.Principal := GlobalTheory.T.principal_siegel_of_generic_principal_special_ample L1 L2 h _ hk hk3 _ _ C O hO p hp hpC β c₁ hgen hamp
    have hp₀ : (restrictBase j hj c₁).Principal := hp₁
    obtain ⟨t, ht⟩ := GlobalTheory.T.exists_thetaObject_eighthPower_principalSiegel L1 L2 h g W J a bas hW hbas _ o b _ _ (restrictBase j hj c₁) hk hk3 hζ hp₀
    have hfrom := GlobalTheory.T.fromC_sharpClass_fibre_of_charZero L1 L2 h g W J a w w' bas hW hbas hw hw' hu N' o b em har _ _ t _ hp₀ ht C
      (spMap (algebraMap O C))
    haveI : IsDomain O := hO.1.isDomain _
    have hdense : Dense (fromSet em (SharpClass (b := b) W a bas em) t) := by
      have hd : DenseRange (PrimeSpectrum.comap (algebraMap O C)) := by
        rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot _).1 hO.1]
        exact bot_le
      exact Dense.mono (fun z hz => ⟨C, inferInstance, _, hz, hfrom⟩) hd
    have hshape : t.Shape Mat κ := by
      obtain ⟨_, _, _, _, _, _, _, tc, -, -, -, -, -, htc⟩ := hfrom
      have hs := (good.shape tc htc).1
      obtain ⟨cc, hcc, hcs⟩ := htc
      exact GlobalTheory.T.eighthPower_shape_depends_only_on_matrices L1 L2 h g W J a bas hW hbas _ o b Mat κ _ _ _ _ cc _ tc t hh inferInstance hcc hp₀ hcs ht hs
    obtain ⟨f, ⟨hf, hm⟩, -⟩ := rep _ _ t inferInstance hdense fun K _ _ x t' hx =>
      (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w w' _ _ _ _ x t t' hx).1 hshape
    have hpb : SiegPB c₁ c f := (pull _ _ (restrictBase j hj c₁) t f hp₀ ht).2 hm
    refine ⟨pullback.lift f (spMap β) hf, pullback.lift_snd _ _ _, ?_⟩
    refine ((GlobalTheory.T.siegelPullback_id_comp_cancel h _ _ _ _ _ _ _ _ _ _ _ _ _ c u c₁ _ _).2 hupb).2 ?_
    rwa [pullback.lift_fst]
  · intro K _ x c₁ m1 m2
    have hp₁ : c₁.Principal := (GlobalTheory.T.siegelPre_pullback_principal_ringChange h (N' ^ 2) _ _ _ _ (RingHom.id _) _ _ _ _ x rfl
      (by rw [spMap_id, Category.comp_id])).2.1 u c₁ m1 hup
    have hp₀ : (restrictBase j hj c₁).Principal := hp₁
    obtain ⟨t, ht⟩ := GlobalTheory.T.exists_thetaObject_eighthPower_principalSiegel L1 L2 h g W J a bas hW hbas _ o b _ _ (restrictBase j hj c₁) hk hk3 hζ hp₀
    have n1 := (pull _ _ (restrictBase j hj c₁) t _ hp₀ ht).1
      (((GlobalTheory.T.siegelPullback_id_comp_cancel h _ _ _ _ _ _ _ _ _ _ _ _ _ c u c₁ _ _).2 hupb).1 m1)
    have n2 := (pull _ _ (restrictBase j hj c₁) t _ hp₀ ht).1
      (((GlobalTheory.T.siegelPullback_id_comp_cancel h _ _ _ _ _ _ _ _ _ _ _ _ _ c u c₁ _ _).2 hupb).1 m2)
    have e : x ≫ pullback.snd _ _ = constPt x ≫ pullback.snd _ _ := by
      rw [constPt_comp]; exact hconst K _
    refine pullback.hom_ext (htan (DualNumber K) _ _ _ t ?_ n1 n2) e
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, e, Category.assoc]

theorem exists_siegelFamily : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → N0 := by
  intro L1 L2 L3 L4 h p n hh hp hn hodd hnp
  obtain ⟨W, hW, hb⟩ := exists_isE8_isSharpBasis
  obtain ⟨bas, hbas⟩ := hb h
  have hinv : (W + W.transpose) * (W + W.transpose)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [hW.2]; exact isUnit_one)
  let a : (Fin 8 × Fin 8) ⊕ Bool → Matrix (Fin 8) (Fin 8) ℤ :=
    Sum.elim (fun uv => Matrix.single uv.1 uv.2 1)
      (fun e => (W + W.transpose)⁻¹ * (if e then W else W.transpose))
  have hw : (W + W.transpose) * a (.inr true) = W := by
    change _ * (_ * W) = W
    rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hw' : (W + W.transpose) * a (.inr false) = W.transpose := by
    change _ * (_ * W.transpose) = W.transpose
    rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hu : ∀ u v, ∃ j, a j = Matrix.single u v 1 := fun u v => ⟨.inl (u, v), rfl⟩
  obtain ⟨Mat, κ, hcl⟩ := GlobalTheory.T.isGoodThetaComplexClass_E8Sharp L1 L2 L3 L4 h _ W _ a _ _ bas hW hbas hw hw' hu
  obtain ⟨j₁, h₁⟩ := hcl n hn hodd
  obtain ⟨j₂, h₂⟩ := GlobalTheory.T.nonempty_thetaFamily_over_open_closure L1 L2 _ _ Mat κ n (.inr true) (.inr false) hn hodd
  obtain ⟨j₃, h₃⟩ := GlobalTheory.T.existsUnique_map_to_thetaFamily_openPart L1 L2 _ _ Mat κ n (.inr true) (.inr false) hn hodd
  obtain ⟨m, hm⟩ : ∃ m, m = j₁ + j₂ + j₃ + 1 := ⟨_, rfl⟩
  have hn3 : 3 ≤ n := by
    have := hn.two_le
    obtain ⟨e, he⟩ := hodd
    omega
  have h3 : 3 ≤ n ^ m := hn3.trans (Nat.le_self_pow (by omega) n)
  obtain ⟨o, _, b, em, j, har, hj, -, hconst⟩ :=
    GlobalTheory.T.exists_cyclotomic_base_ring_inverting_prime n (m * 2) p ((n ^ m) ^ 2) hn hp hnp (by omega) (pow_mul n m 2).symm
  have good := h₁ m (by omega) _ rfl o b em
  obtain ⟨F⟩ := h₂ m (by omega) o b em _ _ har good
  refine ⟨m * 2, hn3.trans (Nat.le_self_pow (by omega) n), ?_⟩
  rw [pow_mul]
  exact nonempty_siegelFamily L1 L2 L3 hh hp hW hbas hw hw' hu h3 hodd.pow j har hj hconst good F
    (h₃ m (by omega) o b em _ _ har good F)

end GlobalTheory.SiegelFromSharp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionHomImageStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_hom_image : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ y N p₀, PairRep ψW k y N p₀ → ∃ v : overW W N ⟶ t.G, v ^ k = 1 ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : Sp F ⟶ N.left), OverGen F (overW W N) x → ∀ q : QkPt P.D.toPre F k, QkPtW.IsPullF F x p₀ q → IsImage P F k q (x ≫ v.left) := by
  first | exact @GlobalTheory.TorsRepMap.exists_repMap | exact GlobalTheory.TorsRepMap.exists_repMap | (intros; apply GlobalTheory.TorsRepMap.exists_repMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientDescendsEtaleSurjectiveCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeQuotient_descends_etale_surjective_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S S' : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (π : S' ⟶ S) (o : Ob D l s) (o' : Ob D l (π ≫ s)) (m : ObjMap o' o π) (K : Set o.t.G.left), admitted l 𝔓 p → HeckeSet D o.t 𝔓 p i K → Etale π → Surjective π → QuasiCompact π → HasQuot o' p (m.toSABMap.φ ⁻¹' K) → HasQuot o p K := by
  first | exact @GlobalTheory.HkFam.hasQuot_descend | exact GlobalTheory.HkFam.hasQuot_descend | (intros; apply GlobalTheory.HkFam.hasQuot_descend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientOfOpenCoverReducedBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeQuotient_of_open_cover_reduced_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o : Ob D l s) (K : Set o.t.G.left), admitted l 𝔓 p → HeckeSet D o.t 𝔓 p i K → (∀ q : S, ∃ (U : S.Opens) (o' : Ob D l (U.ι ≫ s)) (m : ObjMap o' o U.ι), q ∈ U ∧ HasQuot o' p (m.toSABMap.φ ⁻¹' K)) → HasQuot o p K := by
  first | exact @GlobalTheory.hasQuot_of_openCover | exact GlobalTheory.hasQuot_of_openCover | (intros; apply GlobalTheory.hasQuot_of_openCover <;> assumption)
end

