import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TorusAlgebraicOfSectionsOfVeryAmple
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0214
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0093
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimQuotientLeOne
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulMemAdjoinOfMemPowRange
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulPullSec
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaPointDeterminesPolarisedLevel
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsSectionRing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.CardZerosOnTorsionCosetLe

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipalSiegPreComplex
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegelInhabitant

def halves (g : ℕ) : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm)

theorem sum_stdSymp {g : ℕ} (a b : Fin g ⊕ Fin g → ℤ) :
    ∑ i, ∑ j, Out.stdSymp g (halves g i) (halves g j) * b j * a i = omegaStd a b := by
  have l : ∀ a, (halves g (.inl a) : ℕ) = a := fun _ => rfl
  have r : ∀ a, (halves g (.inr a) : ℕ) = g + a := fun _ => rfl
  have ll : ∀ i j, Out.stdSymp g (halves g (.inl i)) (halves g (.inl j)) = 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l]
    split_ifs <;> omega
  have rr : ∀ i j, Out.stdSymp g (halves g (.inr i)) (halves g (.inr j)) = 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, r]
    split_ifs <;> omega
  have lr : ∀ i j, Out.stdSymp g (halves g (.inl i)) (halves g (.inr j)) = if i = j then 1 else 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r, Fin.ext_iff]
    split_ifs <;> omega
  have rl : ∀ i j, Out.stdSymp g (halves g (.inr i)) (halves g (.inl j)) = if i = j then -1 else 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r, Fin.ext_iff]
    split_ifs <;> omega
  simp only [Fintype.sum_sum_type, ll, rr, lr, rl, omegaStd, Finset.sum_sub_distrib]
  simp [sub_eq_add_neg, _root_.mul_comm]

theorem exists_lev_of_rel {k g : ℕ} {G U : Type} [CommGroup G] [CommGroup U] {ze : U}
    (W : G → G → U → Prop) (hW : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, W x y c)
    (hmul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c'))
    (hsymm : ∀ x y c, W x y c → W y x c⁻¹) (v : Fin (2 * g) → G) (hv : ∀ i, v i ^ k = 1)
    (hp : ∀ i j, W (v i) (v j) (ze ^ Out.stdSymp g i j)) :
    ∃ lev : (Fin g ⊕ Fin g → ℤ) → G, (∀ x y, lev (x + y) = lev x * lev y) ∧ (∀ x, lev x ^ k = 1) ∧
      ∀ x y, W (lev x) (lev y) (ze ^ omegaStd x y) := by
  let T : Subgroup G := (powMonoidHom k).ker
  choose w hw hw' using fun x y : T => hW x y x.2 y.2
  have wl : ∀ x x' y, w (x * x') y = w x y * w x' y := fun x x' y =>
    (hw' _ _ _ (hmul _ _ _ _ _ (hw x y) (hw x' y))).symm
  have ws : ∀ x y, w y x = (w x y)⁻¹ := fun x y => (hw' _ _ _ (hsymm _ _ _ (hw x y))).symm
  have wr : ∀ x y y', w x (y * y') = w x y * w x y' := fun x y y' => by
    rw [ws _ x, wl, mul_inv, ← ws, ← ws]
  let e : T →* T →* U := MonoidHom.mk' (fun x => MonoidHom.mk' (w x) (wr x))
    fun x x' => MonoidHom.ext fun y => wl x x' y
  let u : Fin g ⊕ Fin g → T := fun i => ⟨v (halves g i), hv _⟩
  have hu : ∀ i j, e (u i) (u j) = ze ^ Out.stdSymp g (halves g i) (halves g j) := fun i j =>
    (hw' (u i) (u j) _ (hp _ _)).symm
  let l : (Fin g ⊕ Fin g → ℤ) → T := fun a => ∏ i, u i ^ a i
  refine ⟨fun a => (l a).1, fun x y => ?_, fun x => (l x).2, fun x y => ?_⟩
  · rw [← Subgroup.coe_mul]
    congr 1
    simp only [l, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  · have : w (l x) (l y) = ze ^ omegaStd x y := by
      show e (l x) (l y) = _
      have z : ∀ {I : Type} [Fintype I] (n : I → ℤ), ze ^ ∑ i, n i = ∏ i, ze ^ n i := fun n =>
        map_prod (zpowersHom U ze) (fun i => Multiplicative.ofAdd (n i)) _
      have s : ∀ i, e.flip (l y) (u i) = ze ^ ∑ j, Out.stdSymp g (halves g i) (halves g j) * y j := fun i => by
        rw [z, MonoidHom.flip_apply]
        simp only [l, map_prod, map_zpow, hu, ← zpow_mul]
      rw [← sum_stdSymp, ← MonoidHom.flip_apply, z]
      show e.flip (l y) (∏ i, u i ^ x i) = _
      simp only [map_prod, map_zpow, s, ← zpow_mul, Finset.sum_mul]
    exact this ▸ hw _ _

end GlobalTheory.SiegelInhabitant

namespace GlobalTheory

open SiegelInhabitant in

theorem exists_principal_siegPre_complex : ∀ (h k : ℕ), 0 < k → ∀ (o : Type) [CommRing o] (em : o →+* ℂ) (ζ : o), IsPrimitiveRoot (em ζ) k → ∃ c : SiegPre h k ζ (spMap em), c.Principal ∧ SmoothOfRelativeDimension h c.A.hom := by
  intro h k hk o _ em ζ hζ
  have hL : Out.Laws := GlobalTheory.T.all_six_abelian_scheme_laws_hold.1
  obtain ⟨P, -, -, hg, -⟩ := polarisedTorus_algebraic h (Complex.I • (1 : Matrix (Fin h) (Fin h) ℂ)) 0 0
    (Matrix.isSymm_one.smul _)
    (by
      have : (Complex.I • (1 : Matrix (Fin h) (Fin h) ℂ)).map Complex.im = 1 := by
        ext i j
        by_cases e : i = j <;> simp [Matrix.one_apply, e]
      rw [this]
      exact Matrix.PosDef.one)
    (fun _ => Or.inl rfl) (fun _ => Or.inl rfl)
  subst hg
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  let ze : ℂˣ := (hζ.isUnit hk.ne').unit
  have hze : IsPrimitiveRoot ze k := IsPrimitiveRoot.coe_units_iff.1 hζ
  have := P.isAb.comm
  obtain ⟨pt, hpt, hw⟩ := EllipticLevel.exists_symplectic_system hL P k hk' ze hze
  obtain ⟨w₁, w₂, -⟩ := hL.weil _ P k (Out.baseOver _)
  obtain ⟨lev, add, tors, weil⟩ := exists_lev_of_rel (G := Out.baseOver _ ⟶ P.A)
    (fun x y c => Out.WeilIs P.A P.L k x y c) w₁ w₂ (fun _ _ _ h => CommPairing.weilIs_symm P.isLB h) pt hpt hw
  obtain ⟨c, φ, -, hc, -⟩ := exists_siegPre_of_polAV hL GlobalTheory.T.theorem_of_cube_polAbelianScheme o ℂ em P.g k ζ ze P lev rfl hk' rfl hze add tors
    (fun x y => by
      have e : unitOn (ze ^ omegaStd x y) = unitOn ze ^ omegaStd x y := map_zpow (Units.map _) _ _
      rw [e]
      exact weil x y)
  refine ⟨c, hc, ?_⟩
  have := P.smoothDim
  rw [← Over.w φ.hom]
  have : IsIso φ.hom.left := inferInstanceAs (IsIso ((Over.forget _).map φ.hom))
  have H : SmoothOfRelativeDimension (0 + P.g) (φ.hom.left ≫ P.A.hom) := inferInstance
  rwa [Nat.zero_add] at H

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyFromVeryDensePoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem exists_tObj_of_veryDense : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → ∃ t : TObj g ((n ^ j) ^ 2) J b (spMap β), t.HasTh (𝟙 _) v ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → TMap t' t (spMap x) := by
  intro h1 h2 g J _ Mat κ n hn hodd
  obtain ⟨j1, H1⟩ := GlobalTheory.T.exists_theta_scheme_sections_good_fibres h1 h2 g J Mat κ n hn hodd
  obtain ⟨j2, H2⟩ := GlobalTheory.T.exists_family_addition_morphism_thetaLevel h1 h2 g J Mat κ n hn hodd
  obtain ⟨j3, H3⟩ := GlobalTheory.T.exists_inversion_endomorphisms_thetaLevelFamily h1 h2 g J Mat κ n hn hodd
  obtain ⟨j4, H4⟩ := GlobalTheory.T.exists_principallyPolarised_of_veryDense_fibres h1 h2 g J Mat κ n hn hodd
  refine ⟨j1 + j2 + j3 + j4 + 4, ?_⟩
  intro j hj o _ b R _ _ _ β v hv
  obtain ⟨Z, I, M, th, sc, p, hZ, hfib⟩ := H1 j (by omega) o b R β v hv
  obtain ⟨m, hm⟩ := H2 j (by omega) o b R β v Z I M th sc p hv hZ hfib
  obtain ⟨F, hF⟩ := H3 j (by omega) o b R β v Z I M th sc p hv hZ hfib
  obtain ⟨P, act, Q, hP, hgood⟩ := H4 j (by omega) o b R β v Z I M th sc p m F hv hZ hfib hm hF
  obtain ⟨t, ht, hlast⟩ := GlobalTheory.T.exists_square_level_with_given_thetaPoint h1 h2 g n j J hn hodd (by omega) o b R β v P act Q hP (by
    intro q f hq hf
    obtain ⟨p', ⟨K, iK, iK', x, t', hker, hsh, hth⟩, hp'⟩ := hv q f hq hf
    obtain ⟨ψ, hψ⟩ := hgood K x t' hsh hth
    exact ⟨p', ⟨K, iK, iK', x, t', ψ, hker, hth, hψ⟩, hp'⟩)
  refine ⟨t, ht, ?_⟩
  intro K _ _ x t' hsh hth
  obtain ⟨ψ, hψ⟩ := hgood K x t' hsh hth
  exact hlast K x t' ψ hth hψ

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionToG
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.FlatTors

open GlobalTheory.TorusModel GlobalTheory.TorsionFormCompare GlobalTheory.KernelNoTorsion

theorem exists_torsion_toG : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∃ (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), IsFinite N.hom ∧ Flat N.hom ∧ Etale (pullback.snd N.hom (jK R)) ∧ GtTors k g₀ ∧ (∀ (T : Over (Sp R)) (g : GtPt P.D.toPre T), GtTors k g → ∃! h : T ⟶ N, GtPt.IsPull h.left g₀ g) ∧ x₀ ^ k = 1 ∧ FormalEq P.U.toUnifPre x₀ g₀ := by
  intro E _ _ _ H R _ _ _ _ hR t P W _ _ ψW k hk
  obtain ⟨_, -, -, hc⟩ := hR
  have hL := abelianSchemeLaws_all.1
  obtain ⟨Gt, _, _, hH⟩ := exists_isGt hL.globalFns (splitExt P.D.toPre)
  obtain ⟨Φ, hΦ⟩ := exists_points hL.globalFns hH
  have hΦ : Represents Φ := hΦ
  have hfin : IsFinite (torsion Gt k).hom ∧ Flat (torsion Gt k).hom := by
    obtain ⟨h₁, h₂, -⟩ := hL.mulN _ P.D.toPre.P k hk
    have h₁' : IsFinite (𝟙 P.D.toPre.P.A ^ k).left := h₁
    have h₂' : Flat (𝟙 P.D.toPre.P.A ^ k).left := h₂
    rw [← MulEtaleDvr.mulN_eq_pow] at h₁' h₂'
    have Q := MulEtaleDvr.isPullback_torsion P.D.toPre.P.A k
    exact isFinite_flat_torsion_of_isGt _ (splitExt P.D.toPre) Gt hH k hk
      (MorphismProperty.of_isPullback (P := @IsFinite) Q h₁') (MorphismProperty.of_isPullback (P := @Flat) Q h₂')
  obtain ⟨hf, hl⟩ := hfin
  have hs := (GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt _ _ hH).1
  haveI : CharZero (FractionRing R) := (RingHom.charZero_iff (IsFractionRing.injective R _)).1 inferInstance
  have hu : IsUnit (k : Γ(Sp (FractionRing R), ⊤)) :=
    MulEtaleDvr.isUnit_natCast_sections (Nat.cast_ne_zero.mpr (by omega)).isUnit
  have het : Etale (pullback.snd (torsion Gt k).hom (jK R)) := GlobalTheory.LamF.etale_pullback_torsion (jK R) Gt hu
  obtain ⟨J, hJ⟩ := exists_mulEquiv P.U.toUnifPre hL.globalFns hΦ
  have hN := isAdicColimit_of_isFinite hc (torsion Gt k)
  refine ⟨torsion Gt k, Φ _ (torsion.ι Gt k), J _ hN (torsion.ι Gt k), hf, hl, het,
    (tors_iff hΦ k _).2 (torsionι_pow Gt k), fun T g hg => ?_, ?_,
    (formalEq_iff _ _ _).2 ((hJ _ hN _ _).1 rfl)⟩
  · obtain ⟨x, rfl⟩ := (Φ T).surjective g
    have hx := (tors_iff hΦ k x).1 hg
    refine ⟨torsionLift x hx, (isPull_iff_comp hΦ _ _ _).2 (torsionLift_ι _ _), fun h hh => torsion_hom_ext ?_⟩
    rw [torsionLift_ι]
    exact (isPull_iff_comp hΦ _ _ _).1 hh
  · rw [← map_pow, torsionι_pow, map_one]

end GlobalTheory.FlatTors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueIota
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.IotaExists

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorsionFormCompare

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem val_tauW (ψW : PsiOn D W) (a b : D.X) {Z : Scheme.{0}} (r : Z ⟶ W.toScheme) {z : Z} {J}
    (hJ : Good D.P.L z J) :
    val (ψW.tau a b) r z J = val (ψW.psi (a + b)) r z J * (val (ψW.psi a) r z J)⁻¹ * (val (ψW.psi b) r z J)⁻¹ *
      (val (D.rigW W) r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem tauW_symm (ψW : PsiOn D W) (a b : D.X) {Z : Scheme.{0}} (r : Z ⟶ W.toScheme) {z : Z} {J}
    (hJ : Good D.P.L z J) : val (ψW.tau a b) r z J = val (ψW.tau b a) r z J :=
  (val_tauW ψW a b r hJ).trans ((congrArg₂ (· * ·) ((mul_right_comm _ _ _).trans (congrArg₂ (· * ·)
    (congrArg₂ (· * ·) (congrArg (fun x => val (ψW.psi x) r z J) (add_comm a b)) rfl) rfl)) rfl).trans
      (val_tauW ψW b a r hJ).symm)

theorem existsUnique_iota (hB : D.TauBimult) (ψW : PsiOn D W) (T : Over W.toScheme) (y : D.X) :
    ∃! g : GtPt D (overW W T), GtPt.IsIotaW ψW y g := by
  let ρ : overW W T ⟶ TW W := Over.homMk T.hom rfl
  have vv : ∀ χ z J, Good D.P.L z J →
      val (LB.pullGen D.P.L _ _ (ψW.tau y χ) T.hom) (𝟙 (overW W T).left) z J = val (ψW.tau χ y) ρ.left z J :=
    fun χ z J hJ => ((val_pull hJ _ _ _).trans
      (congrArg (fun r => val (ψW.tau y χ) r z J) (Category.id_comp _))).trans (tauW_symm ψW y χ _ hJ)
  obtain ⟨g, hb, hv⟩ := TorusModel.exists_pt (D := D) (T := overW W T) (cP D _ y)
    (fun χ => LB.pullGen D.P.L _ _ (ψW.tau y χ) T.hom)
    (fun χ => pullGen_isGen _ _ _ _ (IotaAdditive.tau_isGen ψW y χ) _) (fun χ U _ h => by
      have p : ∀ x y w v : (TW W).left ⟶ D.P.A.left, ∏ i : ((PUnit ⊕ PUnit) ⊕ PUnit) ⊕ PUnit.{1},
          h (ρ.left ≫ Sum.elim (Sum.elim (Sum.elim (fun _ => x) (fun _ => y)) (fun _ => w)) (fun _ => v) i) ^
            Sum.elim (Sum.elim (Sum.elim (fun _ => (-1 : ℤ)) (fun _ => - -1)) (fun _ => - -1)) (fun _ => -1) i =
          (h (ρ.left ≫ x))⁻¹ * h (ρ.left ≫ y) * h (ρ.left ≫ w) * (h (ρ.left ≫ v))⁻¹ := fun x y w v => by
        simp [Fintype.prod_sum_type]
      refine (p (cP D _ (y + χ)).left (cP D _ y).left (cP D _ χ).left (1 : TW W ⟶ D.P.A).left).trans ?_
      rw [TorusModel.prod_pt, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left,
        comp_cP, comp_cP, comp_cP, MonObj.comp_one, add_comm y χ, cPoint_add, mul_right_comm _ (h (cP D _ y).left)])
    (fun z J hJ => by
      have C : IsCub (th D (T := overW W T) z J) := isCub_cubV D.cub hJ
      have t := IotaAdditive.tau_mul hB ψW 0 0 y ρ hJ
      rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
      exact (vv 0 z J hJ).trans (mul_eq_left.1 t.symm))
    (fun χ χ' z J hJ => (congrArg₂ (· * ·) (vv _ z J hJ) rfl).trans
      ((IotaAdditive.tau_mul hB ψW χ χ' y ρ hJ).trans (congrArg₂ (· * ·) (vv _ z J hJ) (vv _ z J hJ)).symm))
  refine ⟨g, ⟨hb, fun χ => corr_of_val D.P.isLB fun z J hJ => hv χ _ _ z J hJ⟩, fun g' H => ?_⟩
  exact TorusModel.pt_ext (H.1.trans hb.symm) fun χ z J hJ =>
    (val_corr hJ (H.2 χ) (𝟙 _)).trans (hv χ _ _ z J hJ).symm

theorem iota_existsUnique : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ (T : Over W.toScheme) (y : P.D.toPre.X), ∃! g : GtPt P.D.toPre (overW W T), GtPt.IsIotaW ψW y g :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ P _ _ _ ψW _ _ T y => existsUnique_iota P.D.tau_bimult ψW T y

end GlobalTheory.IotaExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinFlatEtSplitTorus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TorusTorsion

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Sp R)}

theorem val_unitGen {X Y Z : Scheme.{0}} {L : LB X} (u : Γ(Y, ⊤)ˣ) (r : Z ⟶ Y) {z : Z} {J} (hJ : Good L z J) :
    val (GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.unitGen L u) r z J = gm r z ⊤ u :=
  gm_res _ z le_top (hJ.mem PEmpty.elim _) _

theorem isGen_unitGen {X Y : Scheme.{0}} (L : LB X) (u : Γ(Y, ⊤)ˣ) : (GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.unitGen L u).IsGen :=
  fun i j => by
    obtain rfl : i = j := funext fun k => k.elim
    exact ((congrArg₂ (· * ·) (Fintype.prod_empty _) rfl).trans (_root_.one_mul _)).symm

theorem TorusVal.val_eq {g : GtPt D T} {χ : D.X} {u : Γ(T.left, ⊤)ˣ} (h : TorusVal g χ u) {Z : Scheme.{0}}
    (r : Z ⟶ T.left) {z : Z} {J} (hJ : Good D.P.L z J) : val (g.s χ) r z J = gm r z ⊤ u :=
  (val_corr hJ h.2 r).trans (val_unitGen u r hJ)

theorem exists_torusPt (u : D.X →+ Additive Γ(T.left, ⊤)ˣ) :
    ∃ g : GtPt D T, ∀ χ, TorusVal g χ (Additive.toMul (u χ)) := by
  obtain ⟨g, hb, hv⟩ := exists_pt (D := D) (T := T) 1 (K := PEmpty) (φ := fun _ => PEmpty.elim) (ε := PEmpty.elim)
    (fun χ => GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.unitGen D.P.L (Additive.toMul (u χ))) (fun χ => isGen_unitGen _ _)
    (fun χ U i h => (GlobalTheory.FieldRestrictionTest.formEq_zero (D := D) (T := T) χ U h).symm)
    (fun y J hJ => by rw [val_unitGen _ _ hJ, map_zero, toMul_zero, map_one]) (fun χ χ' y J hJ => by
      have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      rw [C.face₃, val_unitGen _ _ hJ, val_unitGen _ _ hJ, val_unitGen _ _ hJ, map_add, toMul_add, map_mul,
        _root_.mul_one])
  exact ⟨g, fun χ => ⟨hb, corr_of_val D.P.isLB fun y J hJ => hv χ _ _ y J hJ⟩⟩

theorem isZero_iff' (g : GtPt D T) : g.IsZero ↔ g.b = 1 ∧ ∀ χ y J, Good D.P.L y J → cv g χ y J = 1 :=
  and_congr Iff.rfl (forall_congr' fun _ => ⟨fun h _ _ hJ => (val_corr hJ h _).trans (val_one _),
    fun h => corr_of_val D.P.isLB fun y J hJ => (h y J hJ).trans (val_one _).symm⟩)

theorem exists_nsmul_zero (k : ℕ) (u : D.X →+ Additive Γ(T.left, ⊤)ˣ) (hu : k • u = 0) {g : GtPt D T}
    (hg : ∀ χ, TorusVal g χ (Additive.toMul (u χ))) : ∃ h : GtPt D T, GtPt.IsNsmul k g h ∧ h.IsZero := by
  choose gs hgs using fun i : ℕ => exists_torusPt (D := D) (T := T) (i • u)
  have z : ∀ i : ℕ, i • u = 0 → (gs i).IsZero := fun i hi => (isZero_iff' _).2 ⟨(hgs i 0).1, fun χ y J hJ => by
    have := TorusVal.val_eq (hgs i χ) (𝟙 _) hJ
    rw [hi] at this
    exact this.trans (map_one _)⟩
  refine ⟨gs k, ⟨fun i => gs i, z 0 (zero_smul _ _), fun i => (TorusModel.isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => ?_⟩,
    rfl⟩, z k hu⟩
  · rw [(hgs _ 0).1, (hgs _ 0).1, (hg 0).1]
    exact (_root_.mul_one (1 : T ⟶ D.P.A)).symm
  · have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
    have hb : g.b = 1 := (hg 0).1
    rw [show th D y J (cP D _ χ) (gs (i.castSucc : Fin (k + 1))).b g.b = 1 by rw [hb, C.face₃], _root_.mul_one]
    refine (TorusVal.val_eq (hgs _ χ) _ hJ).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (TorusVal.val_eq (hgs _ χ) _ hJ) (TorusVal.val_eq (hg χ) _ hJ)).symm)
    rw [Fin.val_succ, Fin.val_castSucc, succ_nsmul, AddMonoidHom.add_apply, toMul_add, map_mul]

theorem isPull_of_units (h : T' ⟶ T) {g : GtPt D T} {g' : GtPt D T'} {u : D.X → Γ(T.left, ⊤)ˣ}
    {u' : D.X → Γ(T'.left, ⊤)ˣ} (hg : ∀ χ, TorusVal g χ (u χ)) (hg' : ∀ χ, TorusVal g' χ (u' χ))
    (e : ∀ χ, h.left.appTop.hom (u χ).val = (u' χ).val) : GtPt.IsPull h.left g g' := by
  refine (TorusModel.isPull_iff h g g').2 ⟨?_, fun χ y J hJ => ?_⟩
  · rw [(hg 0).1, (hg' 0).1]
    exact (MonObj.comp_one h).symm
  · refine (TorusVal.val_eq (hg' χ) _ hJ).trans (Eq.trans (Units.ext ?_) (TorusVal.val_eq (hg χ) _ hJ).symm)
    rw [gm_val _ y ⊤ trivial, gm_val _ y ⊤ trivial, ← e χ]
    rfl

variable {W : (Sp R).Opens}

end Points

end GlobalTheory.TorusTorsion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtOfIsFinite
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsMono

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct
open GlobalTheory.TorusModel GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.TorsionFormCompare

theorem hom_ext_of_isFinite {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (T : Over (Sp R))
    [IsFinite T.hom] {X : Scheme.{0}} [IsAffine X] {f g : T.left ⟶ X}
    (h : ∀ e, thickι (maximalIdeal R) e T ≫ f = thickι (maximalIdeal R) e T ≫ g) : f = g := by
  have : IsAffine T.left := isAffine_of_isAffineHom T.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (T.left.isoSpec.inv ≫ T.hom)
  have hf : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hf
  letI : Algebra R Γ(T.left, ⊤) := φ.hom.toAlgebra
  have : Module.Finite R Γ(T.left, ⊤) := hf
  obtain ⟨a, ha⟩ := Spec.map_surjective (T.left.isoSpec.inv ≫ f ≫ X.isoSpec.hom)
  obtain ⟨b, hb⟩ := Spec.map_surjective (T.left.isoSpec.inv ≫ g ≫ X.isoSpec.hom)
  suffices a = b by
    rw [this, hb, cancel_epi, cancel_mono] at ha
    exact ha.symm
  ext s
  rw [← sub_eq_zero, ← Submodule.mem_bot R, ← Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := Γ(T.left, ⊤))
    (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top, Submodule.mem_iInf]
  intro e
  let J : Ideal Γ(T.left, ⊤) := (maximalIdeal R ^ (e + 1)).map φ.hom
  let q : Γ(T.left, ⊤) ⟶ CommRingCat.of (Γ(T.left, ⊤) ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  let σ : CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)) ⟶ CommRingCat.of (Γ(T.left, ⊤) ⧸ J) :=
    CommRingCat.ofHom (Ideal.quotientMap J φ.hom Ideal.le_comap_map)
  have w : (Spec.map q ≫ T.left.isoSpec.inv) ≫ T.hom = Spec.map σ ≫ thick R (maximalIdeal R) e := by
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    exact (congrArg Spec.map (by ext x; rfl)).trans (Spec.map_comp _ _)
  have hl : pullback.lift _ _ w ≫ thickι (maximalIdeal R) e T = Spec.map q ≫ T.left.isoSpec.inv :=
    pullback.lift_fst _ _ _
  have e₁ : a ≫ q = b ≫ q := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ha, hb, ← reassoc_of% hl, ← reassoc_of% hl, reassoc_of% h e]
  have e₂ : a.hom s - b.hom s ∈ J := Ideal.Quotient.eq.1 (congrArg (fun u => u.hom s) e₁)
  refine Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ e)) ?_
  rw [Ideal.smul_top_eq_map]
  exact e₂

theorem mono_torsion : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), IsFinite N.hom → GtTors k g₀ → (∀ (T : Over (Sp R)) (g : GtPt P.D.toPre T), GtTors k g → ∃! h : T ⟶ N, GtPt.IsPull h.left g₀ g) → FormalEq P.U.toUnifPre x₀ g₀ → Mono x₀ := by
  intro E _ _ _ H R _ _ _ _ hR t P W _ _ ψW k _ N g₀ x₀ hN hg hu hF
  have := hR.1
  obtain ⟨Gt, _, _, Φ, hΦ, -⟩ := exists_represents P.D.toPre
  obtain ⟨c₀, rfl⟩ := (Φ N).surjective g₀
  have hc₀ := (tors_iff hΦ k c₀).1 hg
  have hp := (formalEq_iff _ _ _).1 hF
  have univ : ∀ {T} (x : T ⟶ Gt), x ^ k = 1 → ∃! h : T ⟶ N, h ≫ c₀ = x := fun {T} x hx =>
    (existsUnique_congr fun h => isPull_iff_comp hΦ h c₀ x).1 (hu T _ ((tors_iff hΦ k x).2 hx))
  have tz : ∀ {T} (h : T ⟶ N), (h ≫ c₀) ^ k = 1 := fun h => by rw [← MonObj.comp_pow, hc₀, MonObj.comp_one]
  have canc : ∀ {T} {h h' : T ⟶ N}, h ≫ c₀ = h' ≫ c₀ → h = h' := fun {T h h'} e => (univ _ (tz h')).unique e rfl
  have pt : ∀ {T} (h : T ⟶ N), IsPointOf P.U.toUnifPre (Φ T (h ≫ c₀)) (h ≫ x₀) := fun h => hp.pull h (hΦ.1 _ _ h c₀)
  have : IsAffine N.left := isAffine_of_isAffineHom N.hom
  have : IsSeparated t.G.hom := t.semi.separated
  have : IsFinite x₀.left := by
    have : IsFinite (x₀.left ≫ t.G.hom) := by rw [Over.w]; exact hN
    exact IsFinite.of_comp _ t.G.hom
  let Q : Over (Sp R) := Over.mk (pullback.fst x₀.left x₀.left ≫ N.hom)
  have : IsFinite Q.hom := inferInstanceAs (IsFinite (pullback.fst x₀.left x₀.left ≫ N.hom))
  let p₁ : Q ⟶ N := Over.homMk (pullback.fst x₀.left x₀.left) rfl
  let p₂ : Q ⟶ N := Over.homMk (pullback.snd x₀.left x₀.left) (by
    show _ = pullback.fst x₀.left x₀.left ≫ N.hom
    rw [← Over.w x₀, pullback.condition_assoc])
  have hx : p₁ ≫ x₀ = p₂ ≫ x₀ := Over.OverMorphism.ext pullback.condition
  have key : p₁.left = p₂.left := hom_ext_of_isFinite Q fun e => by
    have pl : ∀ w : Q ⟶ N, HasCoords P.U.toUnifPre e (Φ _ (fstG (maximalIdeal R) e Q ≫ w ≫ c₀)) (𝟙 _)
        (thickHom (maximalIdeal R) e (w ≫ x₀)) := fun w => by
      rw [← hasCoords_pull (hΦ.1 _ _ (fstG (maximalIdeal R) e Q) (w ≫ c₀)), Category.id_comp]
      exact (isPointOf_iff_thick _ _ _).1 (pt w) e
    have e₁ := (Φ _).injective (eq_of_hasCoords (pl p₁) (hx ▸ pl p₂))
    rw [← Category.assoc, ← Category.assoc] at e₁
    exact congrArg (·.left) (canc e₁)
  have key' : pullback.fst x₀.left x₀.left = pullback.snd x₀.left x₀.left := key
  refine ⟨fun h h' e => Over.OverMorphism.ext ?_⟩
  have e' : h.left ≫ x₀.left = h'.left ≫ x₀.left := congrArg (·.left) e
  rw [← pullback.lift_fst _ _ e', key', pullback.lift_snd]

end GlobalTheory.TorsMono
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointDeterminesAndEndDeterminedTorsion
section
namespace GlobalTheory

theorem _root_.GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion :
    _root_.GlobalTheory.ThetaPtDeterminesSt ∧ _root_.GlobalTheory.EndDeterminedOnTorsionSt := by
  have hL := _root_.GlobalTheory.allSixLaws
  refine ⟨_root_.GlobalTheory.thetaPt_determines hL.1,
    _root_.GlobalTheory.endDeterminedOnTorsion hL.1 ?_⟩
  exact _root_.GlobalTheory.card_zeros_on_torsion_coset_le hL.1.mulN
    (fun K _ X _ p L hL => _root_.GlobalTheory.SectionRing.exists_sectionRing K X p L hL)
    (_root_.GlobalTheory.PowSec.exists_basis_sections hL.1.globalSectionsRank)
    (_root_.GlobalTheory.veryAmple_lbPow hL.1.ample)
    (_root_.GlobalTheory.exists_mulPull_sec hL.1.mulPull)
    (fun K _ X p g hp U hU hne => _root_.GlobalTheory.SmoothDim.ringKrullDim_affineOpen K X p g hp U hU hne)
    _root_.GlobalTheory.polAV_isIntegral_of_isAlgClosed
    (fun K T _ _ _ _ 𝒜 _ m x hx hne d s hs hpow => _root_.GlobalTheory.isIntegral_adjoin_of_mul_pow_mem K T 𝒜 m x hx hne d s hs hpow)
    _root_.GlobalTheory.graded_bezout_bound

end GlobalTheory
end

