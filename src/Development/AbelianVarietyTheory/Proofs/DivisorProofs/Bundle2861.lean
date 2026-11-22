import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2763
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2551
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2657
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2769
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2768

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueFieldPointPolarisedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem thG_unique_of_polFib : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (K : Type) [Field K] (i : R →+* K), Odd m → IsUnit (m : R) → PolFib G L g x → ∀ (th : SecAt G L (spMap i ≫ x)) (pt : Over.mk (spMap i ≫ x) ⟶ G) (c c' : K), ThG G L ρ m th pt (fn c) → ThG G L ρ m th pt (fn c') → c = c' := by
  intro S G _ _ L ρ hL hρ g m R _ _ x K _ i hm hu hP th pt c c' H H'
  obtain ⟨P, α, -, hp, w, hw⟩ := hP
  obtain ⟨ρ₁, -, hr⟩ := GlobalTheory.Ex.OneGen.exists_rigidificationPullbackCompatibleIso hp hw hL P.isLB hρ
  let T : Over (Sp R) := Over.mk (spMap i)
  let T₀ : Over S := Over.mk (spMap i ≫ x)
  have hτ : 𝟙 (Sp K) ≫ T₀.hom = T.hom ≫ x := Category.id_comp _
  obtain ⟨th₁, hth⟩ := GlobalTheory.ThetaPtMove.exists_secRel hp (T := T) (T₀ := T₀) (𝟙 _) hτ hw hL P.isLB th
  have hsq : pt.left ≫ G.hom = spMap i ≫ x := Over.w pt
  let x₁ : T ⟶ P.A := Over.homMk (hp.1.lift pt.left (spMap i) hsq) (hp.1.lift_snd _ _ _)
  have hx : 𝟙 (Sp K) ≫ pt.left = x₁.left ≫ α := by
    rw [Category.id_comp]; exact (hp.1.lift_fst _ _ _).symm
  have hn : x₁ ^ (m ^ 2) = 1 := by
    have h1 := GlobalTheory.ThetaPtMove.over_pow hp (T := T) (T₀ := T₀) (𝟙 _) hτ hx (m ^ 2)
    rw [H.1] at h1
    have h2 := GlobalTheory.ThetaPtMove.over_one hp (T := T) (T₀ := T₀) (𝟙 _) hτ
    exact Over.OverMorphism.ext (hp.1.hom_ext (h1.symm.trans h2) ((Over.w _).trans (Over.w _).symm))
  have hu' : IsUnit ((m ^ 2 : ℕ) : Γ(Sp R, ⊤)) := by
    rw [Nat.cast_pow, ← map_natCast (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom m, ← map_pow]
    exact (hu.pow 2).map _
  have m1 : ThG P.A P.L ρ₁ m th₁ x₁ ((𝟙 (Sp K) : Sp K ⟶ Sp K).appTop.hom (fn c)) :=
    ThG.move (T := T) (T₀ := T₀) hp (𝟙 _) hτ hw hL P.isLB hr hx hn hth H
  have m2 : ThG P.A P.L ρ₁ m th₁ x₁ ((𝟙 (Sp K) : Sp K ⟶ Sp K).appTop.hom (fn c')) :=
    ThG.move (T := T) (T₀ := T₀) hp (𝟙 _) hτ hw hL P.isLB hr hx hn hth H'
  have e := ThG.unique (T := T) abelianSchemeLaws_all.1 P hm hu' m1 m2
  have e2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom e
  simpa using e2

end GlobalTheory.UMin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFirstJetsLinearIndependent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.MBLow.TRank

theorem main : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → 3 ≤ m → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) → ∀ ϑ J, ThJet x hg m pt ϑ J → ∀ (c₀ : K) (c : Fin g → K), (∀ i, c₀ * ϑ i + ∑ j, c j * J i j = 0) → c₀ = 0 ∧ c = 0 := by
  intro K _ _ _ x g hg m hm hm3 I pt hpt ϑ J hTJ c₀ c hrel
  obtain ⟨th, hth, U, t, i₀, c', hUt, hi₀, hval⟩ := hTJ
  have hg1 : 1 ≤ g := hg ▸ x.g_pos
  let j₀ : Fin g := ⟨0, hg1⟩
  have hy : ∀ j : Fin g, epsLift (x.v (j.cast hg.symm)) ≫ (fst (baseOver (Sp K)) x.P.A).left =
      spMap (algebraMap K (DualNumber K)) := fun j => by
    rw [epsLift, ← Over.comp_left, lift_fst]; rfl
  choose f hf using fun j : Fin g => GlobalTheory.T.exists_linear_sectionValue_abelianPower K x (m ^ 2) (fun _ => i₀) (DualNumber K) _ (hy j)
  set a := c₀ - ∑ j, c j * c' j with ha
  let Φ : EA x.P (𝟙 (Sp K)) (m ^ 2) →ₗ[K] K :=
    a • ((TrivSqZeroExt.fstHom K K K).toLinearMap ∘ₗ f j₀) + ∑ j, c j • (TrivSqZeroExt.sndHom K K ∘ₗ f j)
  have hΦ : ∀ s, Φ s = a * (f j₀ s).fst + ∑ j, c j * (f j s).snd := fun s => by
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
    rfl
  have hft : ∀ j i, f j (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i)) =
      valR (epsLift (x.v (j.cast hg.symm))) ((LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K))).U fun _ => i₀)
        ((t i).f fun _ => i₀) := fun j i => hf j _
  have hΦt : ∀ i, Φ (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i)) = 0 := fun i => by
    rw [hΦ]
    simp only [hft, hval]
    set r := valR (𝟙 (Sp K)) ((x.P.L.pull (eSec x.P.A)).U fun _ => i₀) (x.rig.s fun _ => i₀).val ^ (m ^ 2)
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, smul_eq_mul,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, add_zero, zero_add, mul_zero, zero_mul]
    have e1 : ∑ j, c j * (r * (J i j + c' j * ϑ i)) = r * ∑ j, c j * J i j + r * ϑ i * ∑ j, c j * c' j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, ha]
    linear_combination r * hrel i
  have hspan := GlobalTheory.T.span_thetaTranslates_torsion_eq_top K x m hm hm3 I pt hpt th hth U t hUt
  have hΦ0 : Φ = 0 := LinearMap.ext_on_range hspan fun i => by rw [hΦt i, LinearMap.zero_apply]
  have hsep := GlobalTheory.T.sections_lineBundlePow_separate_firstJets_origin K x g hg (m ^ 2) (by nlinarith) i₀ hi₀ j₀ a c fun s => by
    have h := congrArg (fun F => F (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left s)) hΦ0
    simp only [LinearMap.zero_apply, hΦ] at h
    rw [hf j₀, Finset.sum_congr rfl fun j _ => by rw [hf j]] at h
    exact h
  obtain ⟨h1, h2⟩ := hsep
  refine ⟨?_, h2⟩
  subst h2
  simpa [ha] using h1

end GlobalTheory.MBLow.TRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTranslatedMembersLeadingTimesIntegral
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.ThFam

theorem prod_famB {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
    (ρ : T ⟶ D.P.A) (α : D.X) (k : ℕ) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (ρ.left ≫ D.famφB α i) ^ DegPre.famε k i =
      h ρ.left ^ ((k : ℤ) - 1) * h (DVR.cP D T α * ρ).left * (h (DVR.cP D T α).left)⁻¹ *
        h (1 : T ⟶ D.P.A).left := by
  have e₀ : ρ.left ≫ D.famφB α 0 = ρ.left := Category.comp_id _
  have e₁ : ρ.left ≫ D.famφB α 1 = (DVR.cP D T α * ρ).left := by
    have : ρ ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α) = DVR.cP D T α * ρ := by
      show ρ ≫ (𝟙 _ * DVR.cP D D.P.A α) = _
      rw [MonObj.comp_mul, Category.comp_id, DVR.comp_cP, mul_comm]
    exact congrArg (fun q => q.left) this
  have e₂ : ρ.left ≫ D.famφB α 2 = (DVR.cP D T α).left := congrArg (fun q => q.left) (DVR.comp_cP D ρ α)
  have e₃ : ρ.left ≫ D.famφB α 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_four, e₀, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]

theorem exists_genB : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (k : ℕ) (α mu : D.X) {K : Type} [Fintype K]
    (φ : K → (Spec (CommRingCat.of R) ⟶ D.P.A.left)) (ε : K → ℤ) (v : LB.Gen (LB.LinComb D.P.L φ ε)), v.IsGen →
    (∀ (U : Type) [CommGroup U] (h : (Spec (CommRingCat.of R) ⟶ D.P.A.left) → U), ∏ i, h (φ i) ^ ε i =
      (h (ReciprocityTheory.ChartRestriction.G.DVR.cP D (Over.mk (𝟙 (Spec (CommRingCat.of R)))) (α + mu)).left)⁻¹ *
        h (ReciprocityTheory.ChartRestriction.G.DVR.cP D (Over.mk (𝟙 (Spec (CommRingCat.of R)))) α).left *
        h (ReciprocityTheory.ChartRestriction.G.DVR.cP D (Over.mk (𝟙 (Spec (CommRingCat.of R)))) mu).left *
        (h (1 : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ D.P.A).left)⁻¹ *
        (h (ReciprocityTheory.ChartRestriction.G.DVR.cP D (Over.mk (𝟙 (Spec (CommRingCat.of R)))) mu).left ^ k)⁻¹ *
        h (1 : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ D.P.A).left ^ k) →
    ∃ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB (α + k • mu))
        (fun i => (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c mu)).left ≫ D.famφB α i)) (DegPre.deltaε k)),
      u.IsGen ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ D.P.A) (z : T.left)
        (J : (T.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val u ρ.left z J = ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN (ReciprocityTheory.ChartRestriction.G.DVR.th D z J) k
            (ReciprocityTheory.ChartRestriction.G.DVR.cP D T α) (ReciprocityTheory.ChartRestriction.G.DVR.cP D T mu) ρ *
          (ReciprocityTheory.ChartRestriction.G.DVR.th D z J (ReciprocityTheory.ChartRestriction.G.DVR.cP D T α) ρ (ReciprocityTheory.ChartRestriction.G.DVR.cP D T mu))⁻¹ *
          val v (ρ.left ≫ D.P.A.hom) z J := by
  intro R _ _ D k α mu K _ φ ε v hv hF
  have htr : padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c mu) = (𝟙 D.P.A) * (DVR.cP D D.P.A mu) := rfl
  have hα' : DVR.cP D D.P.A (α + k • mu) = (DVR.cP D D.P.A α) * (DVR.cP D D.P.A mu) ^ k := by rw [DVR.cPoint_add, DVR.cPoint_nsmul]
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub (DVR.cP D D.P.A α) (DVR.cP D D.P.A mu) (𝟙 D.P.A) k
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_gen D.P.isLB (φ' := Sum.elim (D.famφB (α + k • mu))
      (fun i => (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c mu)).left ≫ D.famφB α i)) (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub (DVR.cP D D.P.A α) (𝟙 D.P.A) (DVR.cP D D.P.A mu) h
      have p₂ := hF U (fun q => h (D.P.A.hom ≫ q))
      have p₃ : ∏ i, h (D.famφB (α + k • mu) i) ^ DegPre.famε k i = h (Over.Hom.left (𝟙 D.P.A)) ^ ((k : ℤ) - 1) *
          h ((DVR.cP D D.P.A α) * (DVR.cP D D.P.A mu) ^ k * 𝟙 D.P.A).left *
          (h ((DVR.cP D D.P.A α) * (DVR.cP D D.P.A mu) ^ k).left)⁻¹ * h (1 : D.P.A ⟶ D.P.A).left := by
        have := prod_famB D (𝟙 D.P.A) (α + k • mu) k h
        rw [hα'] at this
        refine Eq.trans ?_ this
        simp only [Over.id_left, Category.id_comp]
      have p₄ := prod_famB D (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c mu)) α k h
      have c₁ : ∀ χ, D.P.A.hom ≫ (DVR.cP D (Over.mk (𝟙 (Spec (CommRingCat.of R)))) χ).left = (DVR.cP D D.P.A χ).left :=
        fun χ => congrArg (fun q => q.left) (DVR.comp_cP D (toUnit D.P.A) χ)
      have c₂ : D.P.A.hom ≫ (1 : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ D.P.A).left = (1 : D.P.A ⟶ D.P.A).left :=
        congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (toUnit D.P.A))
      rw [c₁, c₁, c₁, c₂, DVR.cPoint_add] at p₂
      rw [htr] at p₄
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 8 ⊕ thK) (K' := K) (U := U) _
        (DVR.prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ rfl (DVR.prod_neg _ _ p₁)) p₂)
        (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (DVR.prod_neg _ _ p₄)).symm)
      rw [← _root_.mul_assoc (DVR.cP D D.P.A α), mul_comm (DVR.cP D D.P.A mu) (𝟙 D.P.A)]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (DVR.cP D D.P.A α) (lift (𝟙 D.P.A) (DVR.cP D D.P.A mu))).left)))
      (LB.pullGen D.P.L _ _ v D.P.A.hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hN
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))) (DVR.pullGen_isGen _ _ _ _ hv _))
  refine ⟨u₀, hu₀, fun T ρ z J hJ => ?_⟩
  have h1 := vu₀ _ ρ.left z J hJ
  rw [val_mul hJ] at h1
  erw [val_mul hJ] at h1
  rw [vN T ρ z J hJ] at h1
  erw [val_inv, val_cub D.cub ρ hJ] at h1
  rw [val_pull hJ] at h1
  rw [h1]
  simp only [DVR.comp_cP, Category.comp_id]

theorem exists_readGen : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (κ : D.X → (FractionRing R)ˣ),
    GlobalTheory.ThFam.Reads D κ → ∀ (k : ℕ) (α mu : D.X),
    ∃ (K : Type) (_ : Fintype K) (φ : K → (Spec (CommRingCat.of R) ⟶ D.P.A.left)) (ε : K → ℤ)
      (v : LB.Gen (LB.LinComb D.P.L φ ε)), v.IsGen ∧
      (∀ (U : Type) [CommGroup U] (h : (Spec (CommRingCat.of R) ⟶ D.P.A.left) → U), ∏ i, h (φ i) ^ ε i =
        (h (ReciprocityTheory.ChartRestriction.G.DVR.cP D (Over.mk (𝟙 (Spec (CommRingCat.of R)))) (α + mu)).left)⁻¹ *
          h (ReciprocityTheory.ChartRestriction.G.DVR.cP D (Over.mk (𝟙 (Spec (CommRingCat.of R)))) α).left *
          h (ReciprocityTheory.ChartRestriction.G.DVR.cP D (Over.mk (𝟙 (Spec (CommRingCat.of R)))) mu).left *
          (h (1 : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ D.P.A).left)⁻¹ *
          (h (ReciprocityTheory.ChartRestriction.G.DVR.cP D (Over.mk (𝟙 (Spec (CommRingCat.of R)))) mu).left ^ k)⁻¹ *
          h (1 : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ D.P.A).left ^ k) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z)
        (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val (DegPre.famMult D (FractionRing R) k mu α) r z J =
          GlobalTheory.ThFam.unitAt (r ≫ jFK (R := R) (FractionRing R)) z (GlobalTheory.ThFam.lead κ k α mu) *
            val v (r ≫ jFK (R := R) (FractionRing R) ≫ jK R) z J := by
  intro R _ _ D κ hκ k α mu
  obtain ⟨g, hg, hgv⟩ := hκ
  let T₀ : Over (Spec (CommRingCat.of R)) := Over.mk (𝟙 _)
  let rigR := LB.pullGen D.P.L _ _ D.rig (toUnit T₀).left
  let tauR := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (g (mu + α))
    (LB.invGen D.P.L _ _ (g mu))) (LB.invGen D.P.L _ _ (g α))) (LB.invGen D.P.L _ _ rigR)
  let v := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (g mu) k) tauR)
    (GeneratorPullback.powGen D.P.L _ _ rigR k)
  have hrig : rigR.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ D.rig_gen _
  refine ⟨_, inferInstance, _, _, v, ?_, ?_, ?_⟩
  · exact ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.powGen_isGen _ _ _ _ (hg mu) k)
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
        (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hg _) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hg _)))
        (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hg _))) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ hrig)))
      (ReciprocityTheory.ChartRestriction.G.DVR.powGen_isGen _ _ _ _ hrig k)
  · intro U _ h
    have a₁ : ∀ χ, ptR D χ = (ReciprocityTheory.ChartRestriction.G.DVR.cP D T₀ χ).left := fun _ => rfl
    have a₂ : (toUnit T₀).left ≫ eSec D.P.A = (1 : T₀ ⟶ D.P.A).left := rfl
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
    rw [add_comm mu α]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    module
  · intro Z r z J hJ
    have t₁ : (toUnit (TK R)).left = jK R := by simpa using Over.w (toUnit (TK R))
    have t₂ : (toUnit T₀).left = 𝟙 (Spec (CommRingCat.of R)) := rfl
    have vp : ∀ {K' : Type} [Fintype K'] {φ : K' → (Spec (CommRingCat.of (FractionRing R)) ⟶ D.P.A.left)}
        {ε : K' → ℤ} (t : LB.Gen (LB.LinComb D.P.L φ ε)) (n : ℕ) (r' : Z ⟶ _),
        val (GeneratorPullback.powGen D.P.L φ ε t n) r' z J = val t r' z J ^ n := fun t n r' => map_pow _ _ _
    have vpR : ∀ {K' : Type} [Fintype K'] {φ : K' → (Spec (CommRingCat.of R) ⟶ D.P.A.left)}
        {ε : K' → ℤ} (t : LB.Gen (LB.LinComb D.P.L φ ε)) (n : ℕ) (r' : Z ⟶ _),
        val (GeneratorPullback.powGen D.P.L φ ε t n) r' z J = val t r' z J ^ n := fun t n r' => map_pow _ _ _
    rw [DegPre.famMult, val_pull hJ, val_mul hJ, val_mul hJ, vp, vp, DegPre.tau, val_mul hJ, val_mul hJ, val_mul hJ,
      val_inv, val_inv, val_inv, DegPre.rigK, val_pull hJ, hgv _ _ _ _ _ hJ, hgv _ _ _ _ _ hJ, hgv _ _ _ _ _ hJ]
    simp only [v, tauR, rigR]
    rw [val_mul hJ, val_mul hJ, vpR, vpR, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv,
      val_pull hJ, t₁, t₂]
    simp only [lead, map_mul, map_pow, map_inv, Category.assoc, Category.comp_id]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, smul_add]
    abel

theorem member_integral : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (κ : D.toPre.X → (FractionRing R)ˣ), GlobalTheory.ThFam.Reads D.toPre κ → ∀ (k : ℕ), 1 ≤ k → ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (F : Fam D.toPre (FractionRing R) k), GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α) (D.toPre.famφB α) (DegPre.famε k) b (DegPre.prB D.toPre (FractionRing R)).left (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) → ∀ (mu : D.toPre.X) (r : R), algebraMap R (FractionRing R) r = ((GlobalTheory.ThFam.lead κ k α mu : (FractionRing R)ˣ) : FractionRing R) → ∃ f : D.toPre.SecB k (α + k • mu), GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) (α + k • mu)) (DegPre.famε k) (F.s (α + k • mu)) (D.toPre.famφB (α + k • mu)) (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing R)).left (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) ∧ ∀ e : ℕ, r ∈ maximalIdeal R ^ (e + 1) → VanMod (maximalIdeal R) f e := by
  intro R _ _ _ _ D κ hκ k hk α b F hb mu r hr
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have hL := D.toPre.P.isLB
  obtain ⟨Kv, _, φv, εv, v, hv, hF, hval⟩ := exists_readGen R D.toPre κ hκ k α mu
  obtain ⟨uR, huR, valR⟩ := exists_genB R D.toPre k α mu φv εv v hv hF
  obtain ⟨f₀, hf₀⟩ := exists_sec hL (φ' := D.toPre.famφB (α + k • mu)) (ε' := DegPre.famε k) (fun U _ h => by
      refine Eq.trans (ReciprocityTheory.ChartRestriction.G.DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
        (c := ∏ i, h ((padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c mu)).left ≫ D.toPre.famφB α i) ^ DegPre.famε k i) rfl
        (ReciprocityTheory.ChartRestriction.G.DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
          (c := ∏ i, h (D.toPre.famφB (α + k • mu) i) ^ DegPre.famε k i) rfl (ReciprocityTheory.ChartRestriction.G.DVR.prod_neg _ _ rfl))) ?_
      exact (mul_comm _ _).trans (inv_mul_cancel_right _ _))
    (pullMulSec b (padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c mu)).left uR huR)
  let f : GlobalTheory.FieldBaseChange.SecOver D.toPre.P.A.hom
      (LB.LinComb D.toPre.P.L (D.toPre.famφB (α + k • mu)) (DegPre.famε k)) :=
    (r • (show GlobalTheory.FieldBaseChange.SecOver D.toPre.P.A.hom
      (LB.LinComb D.toPre.P.L (D.toPre.famφB (α + k • mu)) (DegPre.famε k)) from f₀) :
        GlobalTheory.FieldBaseChange.SecOver D.toPre.P.A.hom (LB.LinComb D.toPre.P.L (D.toPre.famφB (α + k • mu)) (DegPre.famε k)))
  refine ⟨f, ?_, ?_⟩
  · have hbF : F.s α = GlobalTheory.FieldBaseChange.pullOver D.toPre.P.L (DegPre.famε k)
        (GlobalTheory.FieldBaseChange.prB_hom D.toPre (FractionRing R)) (GlobalTheory.FieldBaseChange.famφ_prB D.toPre (FractionRing R) α) b := by
      have := (GlobalTheory.FieldBaseChange.secScal_iff (GlobalTheory.FieldBaseChange.prB_hom D.toPre (FractionRing R))
        (GlobalTheory.FieldBaseChange.famφ_prB D.toPre (FractionRing R) α) hL (F.s α) b _ (algebraMap R (FractionRing R))
        (GlobalTheory.FieldBaseChange.bf_hom D.toPre (FractionRing R)) 1).1 hb
      rw [map_one] at this
      exact (this.trans (one_smul _ _)).symm
    refine (GlobalTheory.FieldBaseChange.secScal_iff_val hL _ _ _ _).2 fun y J hJ => ?_
    obtain ⟨⟨uK, huK, hcK⟩, hvK⟩ := ReciprocityTheory.ChartRestriction.G.DVR.gen_fe (D := D.toPre) (F := FractionRing R) hG k mu α
    have e₁ := (secRel_iff hL _ _ _ _ _ _ _ _ _ uK).1 (F.fe mu α uK huK hcK) _ (𝟙 _) y J hJ
    have e₂ := hvK uK huK hcK _ (𝟙 _) y J hJ
    have e₃ := hval _ (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left y J hJ
    have e₄ := valR _ (DegPre.prB D.toPre (FractionRing R)) y J hJ
    have e₅ := hf₀ _ ((DegPre.prB D.toPre (FractionRing R)).left) y J hJ
    have e₆ := sval_pullMulSec b (padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c mu)).left uR huR
      (DegPre.prB D.toPre (FractionRing R)).left y hJ
    have hf := GlobalTheory.FieldBaseChange.sval_smul' (π := D.toPre.P.A.hom) hJ (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing R)).left) r
      (f₀ : GlobalTheory.FieldBaseChange.SecOver D.toPre.P.A.hom _)
    have m₁ : (DegPre.prB D.toPre (FractionRing R)).left ≫
        (padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c mu)).left =
        (DegPre.trF D.toPre (FractionRing R) mu).left ≫ (DegPre.prB D.toPre (FractionRing R)).left := by
      have m₁' : DegPre.prB D.toPre (FractionRing R) ≫ padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c mu) =
          DegPre.trF D.toPre (FractionRing R) mu ≫ DegPre.prB D.toPre (FractionRing R) := by
        rw [ReciprocityTheory.ChartRestriction.G.DVR.trF_eq, ReciprocityTheory.ChartRestriction.G.DVR.tr_pr, ReciprocityTheory.ChartRestriction.G.DVR.comp_cP]
        show DegPre.prB _ _ ≫ (𝟙 _ * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre D.toPre.P.A mu) = _
        rw [MonObj.comp_mul, Category.comp_id, ReciprocityTheory.ChartRestriction.G.DVR.comp_cP]
      exact congrArg (fun q => q.left) m₁'
    have m₂ : (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom =
        (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R) ≫ jK R := by
      rw [Over.w (DegPre.prB D.toPre (FractionRing R)), ← Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)]
      rfl
    have m₃ : ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) k α
        (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre (TF (R := R) (FractionRing R)) mu) (𝟙 _) y J =
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN (ReciprocityTheory.ChartRestriction.G.DVR.th D.toPre y J) k
            (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ α) (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (DegPre.prB D.toPre (FractionRing R)) *
          (ReciprocityTheory.ChartRestriction.G.DVR.th D.toPre y J (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ α) (DegPre.prB D.toPre (FractionRing R))
            (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu))⁻¹ := by
      rw [ReciprocityTheory.ChartRestriction.G.DVR.uVal_id, ReciprocityTheory.ChartRestriction.G.DVR.comp_cP]
    have m₄ : GlobalTheory.FieldBaseChange.constVal ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫
        jFK (R := R) (FractionRing R) ≫ jK R) y r =
        (unitAt ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) y
          (lead κ k α mu)).val := by
      rw [← Category.assoc, GlobalTheory.FieldBaseChange.constVal_specMap, hr, GlobalTheory.FieldBaseChange.constVal,
        gs_eq _ y ⊤ (by trivial)]
      rfl
    have m₅ : gs (𝟙 _) y ⊤ (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) = 1 := by
      rw [gs_eq _ y ⊤ (by trivial)]
      simp only [scal, map_one]
    rw [hf]
    simp only [Category.id_comp, Over.id_left] at e₁ e₂ ⊢
    rw [e₅, e₆, e₄, m₅, _root_.one_mul, e₁, hbF]
    erw [GlobalTheory.FieldBaseChange.sval_pullOver (GlobalTheory.FieldBaseChange.prB_hom D.toPre (FractionRing R))
      (GlobalTheory.FieldBaseChange.famφ_prB D.toPre (FractionRing R) α) b (DegPre.trF D.toPre (FractionRing R) mu).left hJ]
    rw [e₂, e₃, m₃, m₁, m₂, m₄]
    simp only [Units.val_mul]
    ring
  · intro e he j
    have hpf := pullback.condition (f := D.toPre.P.A.hom) (g := thick R (maximalIdeal R) e)
    refine fn_ext fun y hy => ?_
    rw [gs_pull (𝟙 _) _ y _ hy, GlobalTheory.FieldBaseChange.gs_zero' _ y _ hy]
    have key := GlobalTheory.FieldBaseChange.gs_smul (R := R) D.toPre.P.A.hom
      (𝟙 _ ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) y
      (LB.wchart D.toPre.P.L (D.toPre.famφB (α + k • mu)) j) hy r (f₀.f j)
    refine key.trans ?_
    rw [Category.id_comp, hpf,
      GlobalTheory.FieldBaseChange.constVal_specMap, (Ideal.Quotient.eq_zero_iff_mem).2 he]
    simp only [GlobalTheory.FieldBaseChange.constVal, map_zero]
    rw [GlobalTheory.FieldBaseChange.gs_zero' (pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) e)) y ⊤ (by trivial), zero_mul]

end GlobalTheory.ThFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGeneratedStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_nonvanishing_bundle_generated : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → IsProjOver A.hom →
    ∀ (M : LB A.left), M.IsLB → ∀ (g : ℕ) (u : HolUnif A M g) (θ : (Fin g → ℂ) → ℂ), Differentiable ℂ θ →
    (∀ z, θ z ≠ 0) →
    (∀ l ∈ u.Λ, ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U i → θ (z + l) * u.fr i (z + l) = θ z * u.fr i z) →
    HasGen M := by
  first | exact @GlobalTheory.HolUnifSec.hasGen_of_periodic | exact GlobalTheory.HolUnifSec.hasGen_of_periodic | (intros; apply GlobalTheory.HolUnifSec.hasGen_of_periodic <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPointConjAlgClosureAutomorphism
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ThetaConj

def conjHom {R : Type} [CommRing R] [IsDomain R] (σ : Kb R →ₐ[FractionRing R] Kb R) :
    TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R) :=
  Over.homMk (spMap σ.toRingHom) (by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact σ.commutes a)

end GlobalTheory.ThetaConj

open GlobalTheory.ThetaConj GlobalTheory.ThetaCoord in

theorem GlobalTheory.isThetaPt_conj : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (k : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (I : Type) (x x' : I → (TFK (R := R) (Kb R) ⟶ A.A)) (v : I → Kb R), (∀ i, (x' i).left = spMap σ.toRingHom ≫ (x i).left) → IsThetaPt A k x (fun i => GlobalTheory.Ex.fnOf (v i)) → IsThetaPt A k x' (fun i => GlobalTheory.Ex.fnOf (σ (v i))) := by
  intro R _ _ A k σ I x x' v hx H
  have hs : Subsingleton (TFK (R := R) (Kb R)).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (Kb R)))
  have hn : Nonempty (TFK (R := R) (Kb R)).left :=
    inferInstanceAs (Nonempty (PrimeSpectrum (Kb R)))
  let e : Kb R ≃ₐ[FractionRing R] Kb R :=
    AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hi : conjHom σ ≫ conjHom e.symm.toAlgHom = 𝟙 _ := by
    refine Over.OverMorphism.ext ?_
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_id _))
    ext a
    exact e.apply_symm_apply a
  have Q := isThetaPtOver_pull A (isThetaPtOver_of_subsingleton A H) _ _ hi
  have Q' : IsThetaPtOver A k x' (fun i => GlobalTheory.Ex.fnOf (σ (v i))) := by
    convert Q using 2 with a a
    · exact Over.OverMorphism.ext (hx a)
    · exact congrArg (fun q => q.hom (v a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ.toRingHom))
  refine ⟨H.1, H.2.1, fun p => ⟨⊤, trivial, ?_⟩⟩
  let j : TFK (R := R) (Kb R) ⟶ overRes (T := TFK (R := R) (Kb R)) ⊤ :=
    Over.homMk (TFK (R := R) (Kb R)).left.topIso.inv (by
      change _ ≫ Scheme.Opens.ι ⊤ ≫ _ = _
      rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp])
  exact isThetaPtOver_pull A Q' (overResι ⊤) j
    (Over.OverMorphism.ext (TFK (R := R) (Kb R)).left.topIso.hom_inv_id)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTrivialisationCoordinateNeZeroClassicalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTrivialisation_coordinate_ne_zero_classical : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (x : M.Z) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R) (D : DegData R (maximalIdeal R)), (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ α s, PsiCoord D.toPre α s → (ev s : PadicAlgCl p) ≠ 0 := by
  first | exact @GlobalTheory.Poinc.CoordNe.coord_ne_zero | exact GlobalTheory.Poinc.CoordNe.coord_ne_zero | (intros; apply GlobalTheory.Poinc.CoordNe.coord_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaValueProductFormulaDegenerationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_value_product_formula_degeneration : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = (∏ K : ULift.{0} (Finset (Fin 2)), gm ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left) z _ (T.w.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left ≫ tensφ T.pr k), J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left))) ^ ((-1 : ℤ) ^ (2 - K.down.card))) * (∏ i, ∏ j, (cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) * (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j)) * cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) * cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i)) ^ (-W i j)) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j) := by
  first | exact @GlobalTheory.Mum.Tens.tau_periods | exact GlobalTheory.Mum.Tens.tau_periods | (intros; apply GlobalTheory.Mum.Tens.tau_periods <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedGroupEndomorphismTorusViaCharactersStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickenedGroup_endomorphism_torus_via_characters : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a a' : D.P.A ⟶ D.P.A) [IsMonHom a] [IsMonHom a'] (h' : D.X →+ D.X), ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε)), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) → ∀ (F : thickObj R I e G ⟶ thickObj R I e G), IsCoordEnd g a a' h' u F → ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ splitTorus _ D.X, TorusEndOf D.X h' t ∧ g.i ≫ F = t ≫ g.i := by
  first | exact @GlobalTheory.Mum.EndThick.torus_of_isCoordEnd | exact GlobalTheory.Mum.EndThick.torus_of_isCoordEnd | (intros; apply GlobalTheory.Mum.EndThick.torus_of_isCoordEnd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedGroupEndomorphismTransitionCompatStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickenedGroup_endomorphism_transition_compat : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ) (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X) (u : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A a' a) rosatiε)) (F : thickObj R I e G ⟶ thickObj R I e G) (F' : thickObj R I (e + 1) G ⟶ thickObj R I (e + 1) G), IsCoordEnd (U.gt e) a a' h' u F → IsCoordEnd (U.gt (e + 1)) a a' h' u F' → thickMap R I e G ≫ F'.left = F.left ≫ thickMap R I e G := by
  first | exact @GlobalTheory.Mum.EndThick.isCoordEnd_thickMap_compat | exact GlobalTheory.Mum.EndThick.isCoordEnd_thickMap_compat | (intros; apply GlobalTheory.Mum.EndThick.isCoordEnd_thickMap_compat <;> assumption)
end

