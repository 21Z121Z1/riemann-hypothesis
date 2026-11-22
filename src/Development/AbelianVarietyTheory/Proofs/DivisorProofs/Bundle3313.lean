import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3301
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3290
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2718
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBigThetaSysWithAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2704
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2552
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3302
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2997
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3303
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3304
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2723
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupLevelCoverEveryPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.SetupCov
open GlobalTheory.PoincChart

theorem chartAt : ∀ (n N : ℕ) (X Y Z : Scheme.{0}) (sX : X ⟶ Sp (cycAway n)) (sY : Y ⟶ Sp (cycAway N)) (q : Y ⟶ X) (i : X ⟶ Z), IsOpenImmersion i → 0 < n → 0 < N → Smooth sX → Smooth sY → IsFinite q → Etale q → Surjective q → ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (cycAway N) Ω) (_ : ArithBase (cycAway N) Ω) (R : Subalgebra (cycAway N) Ω) (x : Sp R ⟶ Y) (yR : Sp K ⟶ Sp R) (V : Z.Opens) (f : Sp R ⟶ V), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ IsIntegrallyClosed R ∧ x ≫ sY = spMap (algebraMap (cycAway N) R) ∧ yR ≫ x = y' ∧ (∀ w, (spMap R.val.toRingHom ≫ x ≫ q) w ∈ genericPoints X) ∧ ((spMap R.val.toRingHom ≫ x ≫ q ≫ i).stalkMap (genericPoint (Sp Ω))).hom.Finite ∧ IsAffineOpen V ∧ IsFinite f ∧ f ≫ V.ι = x ≫ q ≫ i := GlobalTheory.T.exists_finite_etale_cover_chart_at_field_point

theorem modelAt : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Z : Scheme.{0}) (π : M.Z ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → IsFinite π → ∀ (R : Subalgebra o Ω), (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → IsIntegrallyClosed R → ∀ (V : Z.Opens) (f : Sp R ⟶ V), IsAffineOpen V → IsFinite f → M.pt ≫ π = spMap R.val.toRingHom ≫ f ≫ V.ι → ∃ φ : Sp R ⟶ M.Z, φ ≫ π = f ≫ V.ι ∧ ∀ (P : Sp R) (a b : R), b ∉ P.asIdeal → (a : Ω) / (b : Ω) ∈ M.O (φ P) := GlobalTheory.T.exists_finite_chart_map_to_normal_finite_model

theorem exists_big_ge (g n : ℕ) (hn : 2 ≤ n) (B : ℕ) : ∃ k j₁ : ℕ, 2 ≤ k ∧ B ≤ (n ^ k) ^ 2 ∧ 1 ≤ j₁ ∧ ∀ j ≥ j₁,
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω),
      S.g = g → S.N = (n ^ k) ^ 2 → S.r = n ^ j → S.Big := by
  have lt : ∀ m : ℕ, m < n ^ m := fun m => Nat.lt_pow_self hn
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2))
  set K := max k₀ B with hK
  set N := (n ^ (K + 2)) ^ 2 with hN
  have hN₁ : K + 2 < N := (lt _).trans_le (Nat.le_self_pow two_ne_zero _)
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt
    (2 * ((N ^ g * g.factorial : ℕ) : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)))
  refine ⟨K + 2, j₀ + 6 * (N ^ g * g.factorial) + 1, by omega, ?_, by omega, fun j hj o Ω _ _ _ S hg hS hr => ?_⟩
  · have : B ≤ K := le_max_right _ _
    omega
  have hj' := lt j
  unfold ThetaSys.Big
  rw [hg, hS, hr, ← hN]
  have hk₀K : k₀ ≤ K := le_max_left _ _
  refine ⟨hk₀.trans (by exact_mod_cast (by omega : k₀ < N)), ?_, ?_⟩
  · rw [Nat.cast_mul (n ^ j)]
    exact mul_lt_mul_of_pos_right (hj₀.trans (by exact_mod_cast (by omega : j₀ < n ^ j)))
      (by exact_mod_cast (by omega : 0 < N))
  · exact lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right _ (by omega))

set_option maxHeartbeats 1000000 in

theorem exists_setup_cov : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (Y : Scheme.{0}) (q : Y ⟶ F.X), j₀ ≤ j ∧ IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (X₁ : Setup F W i) (yM : Sp K ⟶ X₁.M.Z), X₁.S.r * X₁.S.N = (l ^ j) ^ 2 ∧ yM ≫ X₁.π = y' ≫ q ≫ i ∧ ∀ a ∈ X₁.S.R, a ∈ X₁.M.O (yM (closedPoint K)) := by
  intro g hg n hn ho F Z z i _ hproj hZn hiz hden W hW hT l hl hln j₀
  have hlo : Odd l := Odd.of_dvd_nat ho hln
  obtain ⟨k, j₁, hk, -, hj₁, big⟩ := exists_big_ge (8 * g) l hl.two_le 0
  obtain ⟨κ, F', q, ⟨-, hζ, hfin, -, -⟩, ⟨hqs, hqfin, hqet, hqsurj, hq⟩, -⟩ :=
    GlobalTheory.SiegLevCover.exists_levelCover g n l (2 * (j₀ + j₁ + k)) F hg hn ho hl hln (by omega)
  refine ⟨j₀ + j₁ + k, F'.X, q, by omega, hqfin, hqsurj, fun K _ y' => ?_⟩
  have hl3 : 3 ≤ l := by
    have h2 := hl.two_le
    have : l ≠ 2 := fun e => by rw [e] at hlo; exact absurd hlo (by decide)
    omega
  have hk3 : 3 ≤ (l ^ (2 * (j₀ + j₁ + k))) ^ 2 :=
    le_trans (le_trans hl3 (Nat.le_self_pow (by omega) _)) (Nat.le_self_pow (by omega) _)
  have hko : Odd ((l ^ (2 * (j₀ + j₁ + k))) ^ 2) := hlo.pow.pow
  obtain ⟨bas, hbas⟩ := exists_isSharpBasis g W hW
  obtain ⟨a, w, w', hw, hw', hs⟩ := EighthPowerFactor.exists_matrices hW.2
  obtain ⟨b, t', hp', hsh'⟩ := exists_sharpOver_cover g n _ F F' κ q (by omega) hk3 hko hζ hqs hq W _ a w w' bas
    hW hbas hw hw' hs
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI := F'.smooth
  haveI : Smooth F'.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F'.s
  obtain ⟨Ω, _, _, _, R, x, yR, V, f, hRfg, hfrac, hRic, hxs, hyR, hgen, hst, hV, hf, hfV⟩ :=
    chartAt n (n * (l ^ (2 * (j₀ + j₁ + k))) ^ 2) F.X F'.X Z F.s F'.s q i inferInstance (by omega)
      (Nat.mul_pos (by omega) (pow_pos (pow_pos hl.pos _) _)) inferInstance inferInstance hqfin hqet hqsurj K y'
  obtain ⟨t, ht⟩ := GlobalTheory.tObj_pull _ (8 * g) _ _ b F'.X (Sp R) F'.s (spMap (algebraMap _ R)) x t' hxs
  have hp : t.Prim w w' :=
    (GlobalTheory.shape_prim_pull_and_descend _ _ _ _ b (fun _ => 0) 0 w w' _ _ _ _ x t' t ht).2.1 hp'
  obtain ⟨ψ, hψ, hψL, -, -⟩ := ht
  have hsh : SharpOver F W t.pol (x ≫ q) := sharpOver_pullback _ _ _ _ F W _ _ t'.pol t.pol q x ψ hsh' hψ hψL
  have := t.ab.comm
  have hS : ZH.HypS t.A t.L := ⟨t.act w, t.act w', t.hom w, t.hom w', hp.1, hp.2.2, hp.2.1⟩
  have hu : IsUnit (l : cycAway (n * (l ^ (2 * (j₀ + j₁ + k))) ^ 2)) := isUnit_of_dvd_unit (Nat.cast_dvd_cast
    ((dvd_pow_self l (by omega : 2 * (j₀ + j₁ + k) ≠ 0)).trans (dvd_pow_self _ two_ne_zero))) b.unit
  haveI : NeZero ((l ^ (2 * (j₀ + j₁ + k))) ^ 2) := ⟨by have := hl.pos; positivity⟩
  obtain ⟨lev₀, -⟩ := GlobalTheory.ThetaSysOfObj.exists_level R t
  have e : (l ^ (2 * (j₀ + j₁ + k))) ^ 2 = (l ^ (2 * (j₀ + j₁)) * (l ^ k) ^ 2) ^ 2 := by ring
  obtain ⟨lev, -⟩ : ∃ lev : Out.Level t.pol ((l ^ (2 * (j₀ + j₁)) * (l ^ k) ^ 2) ^ 2)
      (unitOn (Units.map (algebraMap _ R).toMonoidHom b.ζ)), True := by
    rw [← e]; exact ⟨lev₀, trivial⟩
  obtain ⟨S, ρ, hR, φ, hreg, -, hNS, hrS, hgS, hpb, hL, -⟩ :=
    GlobalTheory.T.exists_thetaSystem_realisation_regular_at_prime _ Ω R hRfg hfrac (yR (IsLocalRing.closedPoint K)).asIdeal (yR (IsLocalRing.closedPoint K)).isPrime t.pol l k (2 * (j₀ + j₁))
      b.ζ hl hlo hk (by omega) hu hS lev
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _
  haveI : IsProper z := ((isProjOver_iff_isProper_and_exists_isAmpleLB z).1 hproj).1
  have hbase : spMap R.val.toRingHom ≫ x ≫ q ≫ F.s = spMap ((algebraMap _ Ω).comp κ) := by
    rw [hqs, ← Category.assoc x, hxs]
    simp only [spMap, ← Spec.map_comp]
    rfl
  have hp0 : (spMap R.val.toRingHom ≫ x ≫ q ≫ i) ≫ z = spMap ((algebraMap _ Ω).comp κ) := by
    simp only [Category.assoc, hiz]
    exact hbase
  obtain ⟨M, π, hMn, hπ, hcomp⟩ := GlobalTheory.T.exists_normal_model_normalisation_dedekind (cycAway n) _ Ω κ ((IsFinite.SpecMap_iff _).1 hfin) Z z
    inferInstance inferInstance inferInstance _ hp0 hst
  obtain ⟨φM, hφπ, hφreg⟩ := modelAt _ Ω M Z π hMn hπ R hfrac hRic V f hV hf (by rw [hcomp, hfV])
  have ef : spMap S.R.val.toRingHom ≫ spMap (Subalgebra.inclusion hR).toRingHom = spMap R.val.toRingHom :=
    (Spec.map_comp (CommRingCat.ofHom (Subalgebra.inclusion hR).toRingHom) (CommRingCat.ofHom S.R.val.toRingHom)).symm
  have hsharp : SharpOver F W ρ.P (spMap (Subalgebra.inclusion hR).toRingHom ≫ x ≫ q) :=
    sharpOver_pullback _ _ _ _ F W _ _ t.pol ρ.P (x ≫ q) _ φ hsh hpb hL
  refine ⟨Setup.mk _ Ω S ρ (big (2 * (j₀ + j₁)) (by omega) _ Ω S (hgS.trans ?_) hNS hrS)
    (spMap (Subalgebra.inclusion hR).toRingHom ≫ x ≫ q) hsharp
    (fun w => by rw [← Category.assoc, ef]; exact hgen w) M (GlobalTheory.IsNormalScheme.of_pred hMn) π hπ
    (by rw [hcomp]; simp only [Category.assoc]; rw [← Category.assoc (spMap S.R.val.toRingHom), ef]) hg hn ho z hproj (GlobalTheory.IsNormalScheme.of_pred hZn) inferInstance hiz hden
    hW hT κ (by rw [Category.assoc, ← Category.assoc (spMap S.R.val.toRingHom), ef]; exact hbase),
    yR ≫ φM, ?_, ?_, ?_⟩
  · rfl
  · show S.r * S.N = _
    rw [hrS, hNS]; ring
  · show (yR ≫ φM) ≫ π = _
    rw [Category.assoc, hφπ, hfV, ← Category.assoc, hyR]
  · intro a ha
    change a ∈ S.R at ha
    obtain ⟨a', b', hb', e⟩ := hreg a ha
    change a ∈ M.O ((yR ≫ φM) (IsLocalRing.closedPoint K))
    rw [e]
    exact hφreg _ a' b' hb'

end GlobalTheory.Poinc.SetupCov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTermsTorusTranslate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.Poinc.Sep.TermsExt
open GlobalTheory.UT.CoefBasic GlobalTheory.UT.TorsionValue

theorem exists_frAt_ratio {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {K : Type} [Field K] [Algebra (FractionRing R) K] {x : TFK (R := R) K ⟶ A.A} {e e' : FrAt x} (he : e.IsGen)
    (he' : e'.IsGen) : ∃ c : K, c ≠ 0 ∧ ∀ z J, Good A.L z J → (val e' (𝟙 _) z J).val =
      @id ((TFK (R := R) K).left.presheaf.stalk z) (cstH (R := R) z c) * (val e (𝟙 _) z J).val := by
  classical
  obtain ⟨z₀⟩ := exists_pt (R := R) (F := K)
  obtain ⟨J₀, hJ₀⟩ := exists_good' A.isLB (z₀ : (TFK (R := R) K).left)
  set u := val e' (𝟙 _) z₀ J₀ * (val e (𝟙 _) z₀ J₀)⁻¹ with hu
  obtain ⟨c, hc⟩ := cstH_surj (R := R) z₀ u.val
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    rw [map_zero] at hc
    have h1 : (1 : (TF (R := R) K).left.presheaf.stalk z₀) = 0 := by
      rw [← u.val_inv, ← hc, zero_mul]
    have := cstH_inj (R := R) z₀ (show cstH (R := R) z₀ 1 = cstH (R := R) z₀ 0 by rw [map_one, map_zero]; exact h1)
    exact one_ne_zero this
  · intro z J hJ
    obtain rfl := pt_eq (R := R) (F := K) z z₀
    have h1 := val_tr he' (𝟙 _) hJ hJ₀
    have h2 := val_tr he (𝟙 _) hJ hJ₀
    have hcomm : ∀ (y : (TFK (R := R) K).left) (P a b : ((TFK (R := R) K).left.presheaf.stalk y)ˣ),
        P * a = a * b⁻¹ * (P * b) := by
      intro y P a b
      rw [_root_.mul_comm P b, ← _root_.mul_assoc, inv_mul_cancel_right, _root_.mul_comm]
    have key : val e' (𝟙 _) z J = u * val e (𝟙 _) z J := by
      rw [h1, h2, hu]
      exact hcomm _ _ _ _
    show _ = cstH (R := R) z c * _
    rw [key, Units.val_mul, hc]

theorem over_scale {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪 : UMem X₁ z₁ act V ev X t δ) {w₀ : W0 𝔪.U.toUnifPre} {g' : GtPtF 𝔪.D.toPre (FractionRing V)}
    {w w' : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b} (hw : w.IsGen) {x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A}
    {e e' : FrAt x} {c : FractionRing V} (hc : c ≠ 0)
    (he : ∀ z J, Good 𝔪.A.L z J → (val e' (𝟙 _) z J).val =
      @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cstH (R := V) z c) * (val e (𝟙 _) z J).val)
    (hv : ∀ z J, Good 𝔪.D.toPre.P.L z J → (val w' (𝟙 _) z J).val = cst (FractionRing V) z c⁻¹ * (val w (𝟙 _) z J).val)
    (h : 𝔪.Over' w₀ g' w x e) : 𝔪.Over' w₀ g' w' x e' := by
  intro k hk wk' hwk' hgen s s' v hexp hval
  obtain ⟨wk, hwkgen, hwk⟩ := GlobalTheory.UT.TorsionValue.exists_frm_pow w hw k
  have hv' : ValAt s x e (c ^ k * v) := by
    intro z J hJ
    rw [hval z J hJ, GlobalTheory.FrameMove.val_powFrame, GlobalTheory.FrameMove.val_powFrame, zpow_natCast, zpow_natCast,
      Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, he z J hJ]
    simp only [id, cst_eq, map_mul, map_pow]
    ring
  have hsum := h k hk wk hwk hwkgen s s' (c ^ k * v) hexp hv'
  have hscale : ∀ j, coef s' g' wk' j = c⁻¹ ^ k * coef s' g' wk j := by
    intro j
    refine GlobalTheory.UT.TorsionValue.coef_scale hwkgen (fun z J hJ => ?_) s' j
    rw [hwk' z J hJ, hwk z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hv z J hJ]
    simp only [cst_eq, map_pow, mul_pow]
  have := sumF_const_mul (c⁻¹ ^ k) hsum
  have hcv : c⁻¹ ^ k * (c ^ k * v) = v := by
    rw [← _root_.mul_assoc, ← mul_pow, inv_mul_cancel₀ hc, one_pow, _root_.one_mul]
  rw [hcv] at this
  have hf : coef s' g' wk' = fun j => c⁻¹ ^ k * coef s' g' wk j := funext hscale
  rw [hf]
  exact this

attribute [local instance] GlobalTheory.TorusExt.gtGroup in

theorem exists_terms_translate : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ T' : (Fin 8 → X) → Unit → V, 𝔪.Terms x₀ (fun _ : Unit => lab c + τ) T' := by
  intro g n F W Z i X₁ z₁ act x₀ _ V _ _ _ ev X _ m t δ 𝔪 C lab _ T hT c τ hτ
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hexp, hg', hTc⟩ := hT
  obtain ⟨χ, hχ1, hχ⟩ := GlobalTheory.T.exists_torusTorsionPoint_of_label_orthogonal g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 τ hτ
  obtain ⟨p₀, hp₀y, hg₀⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor 𝔪.D.3 χ hχ1
  obtain ⟨p, xτ, hpy, hpg, hpq, hxτ⟩ := hχ p₀.g hg₀
  have hxadd := GlobalTheory.T.memberTorsionPoints_additive_label g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x hx (lab c) τ xτ hxτ
  obtain ⟨ρA, hρA, hρfr⟩ := GlobalTheory.T.exists_rigidification_matchingFrames_torsionFrames g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x fr hx hfr
  obtain ⟨hg'o, hwc, hover⟩ := hg' c
  have hadd : (g' c).IsAdd p₀.g (g' c + p₀.g) := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).mpr rfl
  obtain ⟨hb, -⟩ := GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd
  obtain ⟨w₂, hw₂gen, hw₂⟩ : ∃ w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 (g' c + p₀.g).b, w₂.IsGen ∧
      ∀ z J, Good 𝔪.D.toPre.P.L z J → val w₂ (𝟙 _) z J = val (w c) (𝟙 _) z J := by
    generalize (g' c + p₀.g).b = b at hb ⊢
    subst hb
    exact ⟨w c, hwc, fun _ _ _ => rfl⟩
  obtain ⟨e₂, he₂t, he₂o⟩ := GlobalTheory.T.torusExtension_translate_liesOver_product_torsionFrame g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 w₀ hw₀ ρA hρA (x (lab c)) (fr (lab c))
    (hρfr _) (g' c) (w c) hg'o hwc hover χ hχ1 p₀.g hg₀ p xτ hpy hpg hpq (g' c + p₀.g) hadd w₂ hw₂ (x (lab c + τ)) hxadd
  obtain ⟨κ, hκ0, hκ⟩ := exists_frAt_ratio he₂t.2.1 (hfr (lab c + τ)).1
  obtain ⟨w', hw'gen, hw'⟩ := GlobalTheory.UT.TorsionValue.exists_frm_scale w₂ hw₂gen (inv_ne_zero hκ0)
  have hover' := over_scale 𝔪 hw₂gen hκ0 hκ hw' he₂o
  have hrN : 0 < X₁.S.r * X₁.S.N := by
    obtain ⟨j, -, hj⟩ := X₁.ρ.r_eq
    rw [hj, X₁.ρ.N_eq]
    have := X₁.ρ.n_prime.pos
    positivity
  have hκpow : κ ^ ((X₁.S.r * X₁.S.N) ^ 2 * (X₁.S.r * X₁.S.N) ^ 2) = 1 := by
    obtain ⟨z₀⟩ := exists_pt (R := V) (F := FractionRing V)
    obtain ⟨J₀, hJ₀⟩ := exists_good' 𝔪.A.isLB (z₀ : (TFK (R := V) (FractionRing V)).left)
    have h := GlobalTheory.Poinc.DivDeep.torsFrame_two_levels 𝔪.A (hρfr (lab c + τ)) he₂t hJ₀
    rw [div_self', one_pow] at h
    have hk := hκ z₀ J₀ hJ₀
    apply cstH_inj (R := V) z₀
    rw [map_pow, map_one]
    have hq : (val (fr (lab c + τ)) (𝟙 _) z₀ J₀ / val e₂ (𝟙 _) z₀ J₀).val = cstH (R := V) z₀ κ := by
      rw [div_eq_mul_inv, Units.val_mul, hk, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
      rfl
    rw [← hq, ← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hint : ∀ mu : Fin 8 → X, ∃ y : V,
      algebraMap V (FractionRing V) y = κ⁻¹ * (χ (Multiplicative.ofAdd (𝔪.e₈ mu))).val := by
    intro mu
    have hcl : IsIntegrallyClosed V := 𝔪.cn.2.1
    have h1 : (χ (Multiplicative.ofAdd (𝔪.e₈ mu))) ^ (X₁.S.r * X₁.S.N) = 1 := by
      rw [← MonoidHom.pow_apply, hχ1, MonoidHom.one_apply]
    have hpow : (κ⁻¹ * (χ (Multiplicative.ofAdd (𝔪.e₈ mu))).val) ^
        ((X₁.S.r * X₁.S.N) ^ 2 * (X₁.S.r * X₁.S.N) ^ 2 * (X₁.S.r * X₁.S.N)) = 1 := by
      rw [mul_pow, inv_pow, pow_mul, hκpow, one_pow, inv_one, _root_.one_mul, ← Units.val_pow_eq_pow_val, pow_mul', h1,
        one_pow, Units.val_one]
    have hI : IsIntegral V (κ⁻¹ * (χ (Multiplicative.ofAdd (𝔪.e₈ mu))).val) := by
      refine IsIntegral.of_pow (Nat.mul_pos (Nat.mul_pos (pow_pos hrN 2) (pow_pos hrN 2)) hrN) ?_
      rw [hpow]
      exact isIntegral_one
    exact IsIntegrallyClosed.isIntegral_iff.mp hI
  choose y hy using hint
  have hcoef : ∀ mu, coef s (g' c + p₀.g) w' (𝔪.e₈ mu) =
      κ⁻¹ * (χ (Multiplicative.ofAdd (𝔪.e₈ mu))).val * coef s (g' c) (w c) (𝔪.e₈ mu) := by
    intro mu
    refine GlobalTheory.UT.ThetaAverage.coef_translate hg₀ hadd hwc (fun z J hJ => ?_) s (𝔪.e₈ mu)
    rw [hw' z J hJ, hw₂ z J hJ, cst_eq]
  have hg₂o : ∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c + p₀.g) o ∧ o.IsZero := by
    obtain ⟨o, ho, hoz⟩ := hg'o
    rw [GlobalTheory.TorusExt.isNsmul_iff_eq] at ho
    rw [GlobalTheory.TorusExt.isZero_iff_eq] at hoz
    refine ⟨0, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).mpr ?_, (GlobalTheory.TorusExt.isZero_iff_eq _).mpr rfl⟩
    rw [smul_add, ← ho, hoz, zero_add, GlobalTheory.TorusExt.qk_nsmul 𝔪.D.3 p₀, hp₀y, map_zero]
  refine ⟨fun mu _ => y mu * T mu c, x, fr, th, w₀, s, fun _ => g' c + p₀.g, fun _ => w', hx, hfr, hth, hw₀, hexp,
    fun _ => ⟨hg₂o, hw'gen, hover'⟩, fun mu _ => ?_⟩
  rw [map_mul, hy mu, hcoef mu, ← hTc mu c]
  ring

end GlobalTheory.Poinc.Sep.TermsExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitUniformisationMumfordBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trait_uniformisation_mumfordBundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G.left) (βW₂ : (G2 GW).left ⟶ (G2 G).left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G (spMap φ) βW ∧ Geo.Tor.IsSquare βW βW₂ ∧ LBIso (abelian₂ GW UW.LG.L) (PP.pull βW₂) := by
  first | exact @GlobalTheory.Mum.TraitUnif.exists_trait_unif_lam | exact GlobalTheory.Mum.TraitUnif.exists_trait_unif_lam | (intros; apply GlobalTheory.Mum.TraitUnif.exists_trait_unif_lam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFiniteExtensionSiegelFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisation_finiteExtension_siegelFamily : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁]
    [IsLocalRing V₁], GlobalTheory.LN.CDvr V₁ → ∀ (y₁ : Sp (FractionRing V₁) ⟶ F.X) (A : PolAV (Sp (FractionRing V₁)))
    (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
    IsGrpPullback A.A F.univ.A y₁ α → IsSquare α α₂ → LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) →
    ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G] (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
    IsSemiAbelian G → IsMonHom gen.hom →
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (f : V₁ →+* W)
        (fK : FractionRing V₁ →+* FractionRing W), GlobalTheory.LN.CDvr W ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        (∀ a, fK (algebraMap V₁ _ a) = algebraMap W _ (f a)) ∧
        ∃ (G' : Over (Sp W)) (_ : GrpObj G') (_ : IsCommMonObj G') (D : DegData W (maximalIdeal W))
          (A' : PolAV (Sp (FractionRing W))) (_ : Unif (maximalIdeal W) D A' G') (α' : A'.A.left ⟶ F.univ.A.left)
          (α₂' : (G2 A'.A).left ⟶ (G2 F.univ.A).left),
          IsSemiAbelian G' ∧ IsGrpPullback A'.A F.univ.A (spMap fK ≫ y₁) α' ∧ IsSquare α' α₂' ∧
          LBIso (abelian₂ A'.A A'.L) (F.univ.P.pull α₂') := by
  first | exact @GlobalTheory.PoincUnif.exists_unif_finExt | exact GlobalTheory.PoincUnif.exists_unif_finExt | (intros; apply GlobalTheory.PoincUnif.exists_unif_finExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClassNumberCentraliserTorusSeparableStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_classNumber_centraliserTorus_separable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (K' : Subgroup (Gr G 1)), Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → ∀ (y₀ : grp G β), (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable → (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n → ∀ r : G.GAf × Gr G 1, ∃ R : Finset (G.GAf × Gr G 1), ∀ c : G.GAf × Gr G 1, c * (toAfF G β x t hx y₀, toP1 G β y₀) = (toAfF G β x t hx y₀, toP1 G β y₀) * c → ∃ y : grp G β, y * y₀ = y₀ * y ∧ ∃ s ∈ R, ∃ k : G.GAf × Gr G 1, k.1 ∈ L.K.toSubgroup ∧ k.2 ∈ K' ∧ c * r = (toAfF G β x t hx y, toP1 G β y) * s * k := by
  first | (exact @GlobalTheory.CentCls.main) | (exact GlobalTheory.CentCls.main) | (intros; apply GlobalTheory.CentCls.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetDefiniteHermitianFormLevelStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_doubleCoset_definiteHermitianForm_level : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (K' : Subgroup (Gr G 1)),
  Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ B : GlobalTheory.LKDef.DForm G,
    Finite (DoubleCoset.Quotient (B.emb.range : Set (G.GAf × Gr G 1))
      ((L.K.toSubgroup.prod K' : Subgroup (G.GAf × Gr G 1)) : Set (G.GAf × Gr G 1))) := by
  first | (exact @GlobalTheory.DefClassFin.finite_doubleCoset) | (exact GlobalTheory.DefClassFin.finite_doubleCoset) | (intros; apply GlobalTheory.DefClassFin.finite_doubleCoset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullFourthStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_chern_integral_pull_fourth : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    (∀ α : (hY.atlas σ).Fld, (hY.atlas σ).IsForm α → ∀ ε : ℤˣ, Integrable (fun y => Real.log (1 - v y) / 2) ((hY.atlas σ).part α ε)) ∧
      ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ →
        wInt (hY.atlas σ) (fun y => Real.log (1 - v y) / 2) (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 0 - X 3) * pullF hB hY σ π w φ) = 1 / 2 * (hB.atlas σ).integral φ := by
  first | exact @GlobalTheory.FibLog.wInt_log_one_sub | exact GlobalTheory.FibLog.wInt_log_one_sub | (intros; apply GlobalTheory.FibLog.wInt_log_one_sub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSuccessiveProjectionStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_successive_projection : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (B : Scheme.{0}) (q : B ⟶ Sp k), IsProjOver q →
    ∀ (Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι]
    (E : ι → B.Modules) (r : ι → ℕ), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) →
    ∀ (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl →
    ∀ (a : ι) (i i' : Fin (r a)), (i' : ℕ) = i + 1 →
    ∃ (Y₁ : Scheme.{0}) (σ : Y₁ ⟶ B) (ρ : Y ⟶ Y₁) (wσ : ρ ≫ σ = π) (S P E₁ : Y₁.Modules) (s : S ⟶ P)
      (j : P ⟶ (Scheme.Modules.pullback σ).obj (E a)) (t : P ⟶ E₁) (wst : s ≫ t = 0)
      (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2) (A₀ A₁ : (Σ b, Fin (r b)) → Y₁.Modules)
      (u : ∀ z, A₀ z ⟶ A₁ z) (v : ∀ z, A₁ z ⟶ (Scheme.Modules.pullback σ).obj (E z.1)),
      IsProjOver (σ ≫ q) ∧
      IsFlagBundle ρ (fun _ : Unit => E₁) (fun _ => 2) (fun _ => fl₁) ∧
      (ShortComplex.mk s t wst).ShortExact ∧ GlobalTheory.VB.IsSubbundle s ∧ GlobalTheory.VB.IsSubbundle j ∧ GlobalTheory.VB.IsVB S i ∧
      GlobalTheory.VB.IsVB P ((i : ℕ) + 2) ∧ GlobalTheory.VB.IsVB E₁ 2 ∧
      (∃ e : (Scheme.Modules.pullback ρ).obj P ≅ (fl a).F i'.succ, e.hom ≫ (fl a).ι i'.succ =
        (Scheme.Modules.pullback ρ).map j ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app (E a) ≫
          (Scheme.Modules.pullbackCongr wσ).hom.app (E a)) ∧
      (∃ e : (Scheme.Modules.pullback ρ).obj S ≅ (fl a).F i.castSucc, e.hom ≫ (fl a).ι i.castSucc =
        (Scheme.Modules.pullback ρ).map (s ≫ j) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app (E a) ≫
          (Scheme.Modules.pullbackCongr wσ).hom.app (E a)) ∧
      (∃ (x : (fl a).F i.succ ⟶ (Scheme.Modules.pullback ρ).obj P) (g : (fl a).F i.succ ⟶ fl₁.F 1),
        x ≫ (Scheme.Modules.pullback ρ).map j ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app (E a) ≫
          (Scheme.Modules.pullbackCongr wσ).hom.app (E a) = (fl a).ι i.succ ∧
        g ≫ fl₁.ι 1 = x ≫ (Scheme.Modules.pullback ρ).map t ∧ Epi g) ∧
      ∀ z : Σ b, Fin (r b), z ≠ ⟨a, i⟩ → z ≠ ⟨a, i'⟩ →
        GlobalTheory.VB.IsSubbundle (u z) ∧ GlobalTheory.VB.IsSubbundle (v z) ∧ GlobalTheory.VB.IsVB (A₀ z) z.2 ∧
        GlobalTheory.VB.IsVB (A₁ z) ((z.2 : ℕ) + 1) ∧
        (∃ e : (Scheme.Modules.pullback ρ).obj (A₁ z) ≅ (fl z.1).F z.2.succ, e.hom ≫ (fl z.1).ι z.2.succ =
          (Scheme.Modules.pullback ρ).map (v z) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app (E z.1) ≫
            (Scheme.Modules.pullbackCongr wσ).hom.app (E z.1)) ∧
        (∃ e : (Scheme.Modules.pullback ρ).obj (A₀ z) ≅ (fl z.1).F z.2.castSucc, e.hom ≫ (fl z.1).ι z.2.castSucc =
          (Scheme.Modules.pullback ρ).map (u z ≫ v z) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app (E z.1) ≫
            (Scheme.Modules.pullbackCongr wσ).hom.app (E z.1)) := by
  first | exact @GlobalTheory.OmitFlag.main | exact GlobalTheory.OmitFlag.main | (intros; apply GlobalTheory.OmitFlag.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleTotalSpaceIrreducible
section
set_option autoImplicit false

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits

namespace GlobalTheory.CovTest

theorem IsFlagBundle.geometricallyIrreducible {B Y : Scheme.{0}} {π : Y ⟶ B} {ι : Type} [Fintype ι] {E : ι → B.Modules}
    {r : ι → ℕ} {fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)} (hE : ∀ a, GlobalTheory.VB.IsVB (E a) (r a))
    (hF : IsFlagBundle π E r fl) : GeometricallyIrreducible π := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  obtain ⟨fl', h'⟩ := GlobalTheory.T.flag_bundle_exists_after_base_change B Y _ π x ι E r fl hF
  exact GlobalTheory.T.flag_bundle_over_field_irreducible K _ (pullback.snd π x) ι _ r fl' (fun a => (hE a).pullback x) h'

theorem IsFlagBundle.irreducibleSpace : ∀ (B Y : Scheme.{0}) [IsIntegral B] [IsLocallyNoetherian B] (π : Y ⟶ B) (ι : Type)
    [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)),
    (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → IrreducibleSpace Y := by
  intro B Y _ _ π ι _ E r fl hE hF
  have := hF.geometricallyIrreducible hE
  have := GlobalTheory.T.flag_bundle_universally_open B Y π ι E r fl hE hF
  exact GeometricallyIrreducible.irreducibleSpace π π.isOpenMap

end GlobalTheory.CovTest
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagStatementHoldsStatement
section
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_statement_holds : FlagSt := by
  first | exact @GlobalTheory.DetHT.FlagNorm.flagSt_holds | exact GlobalTheory.DetHT.FlagNorm.flagSt_holds | (intros; apply GlobalTheory.DetHT.FlagNorm.flagSt_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallMemRegularChartIffHeightOnePrimesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forall_mem_regularChart_iff_heightOne_primes : ∀ (σ : Setup) (u : σ.A.left.functionField), (∀ x : Sp σ.R, u ∈ σ.W x) ↔ ∀ p : Sp σ.R, p.asIdeal.height = 1 → σ.f ∈ p.asIdeal → u ∈ σ.W p := by
  first | exact @GlobalTheory.Desc.Setup.forall_mem_W_iff | exact GlobalTheory.Desc.Setup.forall_mem_W_iff | (intros; apply GlobalTheory.Desc.Setup.forall_mem_W_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodForSquareZeroLiftClassificationOfAbelianScheStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodForSquareZeroLiftClassification_of_abelianScheme : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Good A.hom := by
  first | exact @GlobalTheory.LiftSys.good_of_isAbelianScheme | exact GlobalTheory.LiftSys.good_of_isAbelianScheme | (intros; apply GlobalTheory.LiftSys.good_of_isAbelianScheme <;> assumption)
end

