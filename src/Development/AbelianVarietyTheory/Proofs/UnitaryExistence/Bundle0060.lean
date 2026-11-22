import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0057
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0059

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnExponentialFrameMatrixStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_exponential_frame_matrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k) (R : Type) [CommRing R] [Algebra c.F R] (y₀ : FrPt Xo c R) (B : Set (Fin T.m → ℂ)) (ψ : (Fin T.m → ℂ) → (R →ₐ[c.F] CAt σ)) (κ : (Fin T.m → ℂ) → ℂ) (z y : (Fin T.m → ℂ) → FrPt Xo c (CAt σ)) (G : (Fin T.m → ℂ) → (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))) (a : (Fin T.m → ℂ) → CAt σ), IsOpen B → B ⊆ T.co ⁻¹' (M.X k).dom → (∀ t : R, DifferentiableOn ℂ (fun b => toC (ψ b t)) B) → (∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (G b) (a b) (z b) (y b) ∧ IsThetaPt T b (κ b) (y b)) → ∀ τ i j, DifferentiableOn ℂ (fun b => toC (G b τ i j)) B := by
  first | exact @GlobalTheory.HolFrameMatrix.differentiableOn_frameMatrix | exact GlobalTheory.HolFrameMatrix.differentiableOn_frameMatrix | (intros; apply GlobalTheory.HolFrameMatrix.differentiableOn_frameMatrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionNowhereZeroOfPullbackTripleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibreSection_nowhereZero_of_pullbackTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (t' : SAB H (Sp S)) (m : SABMap t' Xo.univ.t x) (th : t'.PP.L.Sec), (∀ y : Sp S, ∃ q : t'.G.left, t'.G.hom q = y ∧ q ∈ Out.nonzeroLocus th) → ∃ s : LB.Sec (PPx x), SecNZ x s := by
  first | exact @GlobalTheory.SecTransport.exists_sec_nonzero | exact GlobalTheory.SecTransport.exists_sec_nonzero | (intros; apply GlobalTheory.SecTransport.exists_sec_nonzero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsObjOfUniformisedTripleComplex
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.UnifObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def negZeta (n : ℕ) : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) / n)) (Complex.exp_ne_zero _)

theorem negZeta_prim {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (negZeta n) n := by
  rw [← IsPrimitiveRoot.coe_units_iff]
  have := (Complex.isPrimitiveRoot_exp n hn.ne').inv
  rwa [← Complex.exp_neg, ← neg_div] at this

theorem negZeta_pow {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : negZeta (n * m) ^ m = negZeta n := by
  have h₁ : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have h₂ : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, negZeta, negZeta, Units.val_mk0, Units.val_mk0, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem negZeta_zpow (n : ℕ) (j : ℤ) :
    ((negZeta n ^ j : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (j : ℂ) / n) := by
  rw [Units.val_zpow_eq_zpow_val, negZeta, Units.val_mk0, ← Complex.exp_int_mul]
  congr 1
  ring

theorem exists_tateIso (D D' : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P' : D'.La →+ (Fin g → ℂ))
    {Q : Type} [Group Q] (act : 𝓞 E → Q → Q) (w : ℕ → Q → Q → ℂˣ → Prop) (e : (Fin g → ℂ) → Q)
    (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (hlin : ∀ (a : 𝓞 E) x i, P' (a • x) i = ty i (a : E) * P' x i)
    (hinj : Function.Injective P') (hadd : ∀ z z', e (z + z') = e z * e z') (hsur : Function.Surjective e)
    (hker : ∀ z, e z = 1 ↔ z ∈ P'.range) (hact : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = act a (e z))
    (hw : ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) →
      w k (e ((k : ℂ)⁻¹ • P' a)) (e ((k : ℂ)⁻¹ • P' b)) c)
    (htow : ∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e)
    (hbij : ∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e)
    (hiso : ∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - D.EF a a') :
    ∃ I : TateIso D ℂ Q act w, ∀ n a, I.ev n a = e ((n : ℂ)⁻¹ • P' (f n a)) := by
  have e0 : e 0 = 1 := (hker 0).2 (zero_mem _)
  have epow : ∀ (m : ℕ) z, e z ^ m = e ((m : ℂ) • z) := fun m z => by
    induction m with
    | zero => simp [e0]
    | succ m ih => rw [pow_succ, ih, ← hadd, Nat.cast_succ, add_smul, one_smul]
  have eP : ∀ a, e (P' a) = 1 := fun a => (hker _).2 ⟨a, rfl⟩
  have div : ∀ n : ℕ, 0 < n → ∀ a, (n : ℂ)⁻¹ • P' (n • a) = P' a := fun n hn a => by
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (Nat.cast_ne_zero.2 hn.ne')]
  have md : ∀ n : ℕ, 0 < n → ∀ a c, e ((n : ℂ)⁻¹ • P' (a + n • c)) = e ((n : ℂ)⁻¹ • P' a) := fun n hn a c => by
    rw [map_add, smul_add, hadd, div n hn, eP, _root_.mul_one]
  refine ⟨{ ζ := negZeta
            ζ_prim := fun n hn => negZeta_prim hn
            ζ_pow := fun n m hn hm => negZeta_pow hn hm
            ev := fun n a => e ((n : ℂ)⁻¹ • P' (f n a))
            add := fun n a b => by rw [map_add, map_add, smul_add, hadd]
            lin := fun n c a => ?_
            ker := fun n hn a => ?_
            onto := fun n hn x => ?_
            tower := fun n m hn hm a => ?_
            isom := fun n hn a b => hw n _ _ _ hn ?_ }, fun _ _ => rfl⟩
  · rw [← hact, map_smul]
    congr 1
    funext i
    rw [Pi.smul_apply, Pi.smul_apply, hlin, smul_eq_mul, smul_eq_mul, mul_left_comm]
  · rw [← (hbij n hn).1, hker]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, hinj ?_⟩
      rw [map_nsmul, hc, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 hn.ne')]
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [hc, div n hn]⟩
  · constructor
    · intro hx
      obtain ⟨z, rfl⟩ := hsur x
      rw [epow, hker] at hx
      obtain ⟨a', ha'⟩ := hx
      obtain ⟨a, c, rfl⟩ := (hbij n hn).2 a'
      exact ⟨a, by rw [← md n hn _ c, ha', inv_smul_smul₀ (Nat.cast_ne_zero.2 hn.ne')]⟩
    · rintro ⟨a, rfl⟩
      rw [epow, smul_inv_smul₀ (Nat.cast_ne_zero.2 hn.ne'), eP]
  · obtain ⟨c, hc⟩ := htow n m hn hm a
    have h₂ : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    rw [epow, smul_smul, ← md n hn _ c, ← hc, Nat.cast_mul, mul_inv, mul_left_comm, mul_inv_cancel₀ h₂,
      _root_.mul_one]
  · rw [← negZeta_zpow]
    congr 1
    obtain ⟨j, hj⟩ := hiso n hn a b
    rw [sub_eq_iff_eq_add.1 hj, zpow_add, zpow_mul, zpow_natCast, (negZeta_prim hn).pow_eq_one, one_zpow,
      _root_.one_mul]

def tateExtend {D : Datum H} {k K : Type} [Field k] [Field K] (φ : k →+* K) {Q Q' : Type} [Group Q] [Group Q']
    {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'} {w : ℕ → Q → Q → kˣ → Prop} {w' : ℕ → Q' → Q' → Kˣ → Prop}
    (I : TateIso D k Q act w) (j : Q →* Q') (hj : Function.Injective j)
    (htor : ∀ n : ℕ, 0 < n → ∀ y, y ^ n = 1 → ∃ x, j x = y) (hact : ∀ a x, j (act a x) = act' a (j x))
    (hw : ∀ n x y c, w n x y c → w' n (j x) (j y) (Units.map φ.toMonoidHom c)) : TateIso D K Q' act' w' where
  ζ n := Units.map φ.toMonoidHom (I.ζ n)
  ζ_prim n hn := (I.ζ_prim n hn).map_of_injective (Units.map_injective φ.injective)
  ζ_pow n m hn hm := by rw [← map_pow, I.ζ_pow n m hn hm]
  ev n a := j (I.ev n a)
  add n a b := by rw [I.add, map_mul]
  lin n c a := by rw [I.lin, hact]
  ker n hn a := by rw [← I.ker n hn, map_eq_one_iff j hj]
  onto n hn y := by
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := htor n hn y hy
      rw [← map_pow, map_eq_one_iff j hj] at hy
      obtain ⟨a, rfl⟩ := (I.onto n hn x).1 hy
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      rw [← map_pow, (I.onto n hn _).2 ⟨a, rfl⟩, map_one]
  tower n m hn hm a := by rw [← map_pow, I.tower n m hn hm]
  isom n hn a b := by
    rw [← map_zpow]
    exact hw _ _ _ _ (I.isom n hn a b)

theorem unitOn_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (c : Aˣ) :
    Units.map (spMap φ).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map φ.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom (c : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm

theorem exists_smul_eq {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] {I J : Ideal O} {n : ℕ}
    (h : I * J = Ideal.span {(n : O)}) {c : O} (hc : c ∈ I) {a : M} (ha : a ∈ J • (⊤ : Submodule O M)) :
    ∃ b : M, c • a = n • b := by
  have := Submodule.smul_mem_smul hc ha
  rw [← Submodule.mul_smul, h, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at this
  obtain ⟨b, -, hb⟩ := this
  exact ⟨b, by rw [← hb, Nat.cast_smul_eq_nsmul]⟩

theorem exists_obj (hL : Out.Laws) {D : Datum H} {l : Level H} (hA : l.A = 1) {B k : Type} [CommRing B] [Field k]
    [IsAlgClosed k] [CharZero k] (b : Base l B) (σ : B →+* k) (t : SAB H (Sp k)) {g : ℕ} (hp : IsProper t.G.hom)
    (hg : SmoothOfRelativeDimension g t.G.hom) (ha : Out.RelAmple t.G t.PP.L) (hk : Out.KTriv t.G t.PP.L)
    (hdet : DetCond D t.act (𝟙 (Sp k)) (σ b.ρ))
    (I : TateIso D k (𝟙_ (Over (Sp k)) ⟶ t.G) (fun a x => x ≫ t.act.act a)
      (fun n x y c => Out.WeilIs t.G t.PP.L n x y (unitOn c))) :
    ∃ (o : Obj D l b (spMap σ)) (m : SABMap t o.t (𝟙 _)),
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        (I.ev l.M a).left ≫ m.φ = (o.eta a).left := by
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨u, hu, π, hπ, huπ⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 l.coprime)
  have hη : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      I.ev l.M (π • a) = I.ev l.M a := fun a h => by
    conv_rhs => rw [← one_smul (𝓞 E) a, ← huπ, add_smul, I.add,
      (I.ker _ hM _).2 (exists_smul_eq l.prod hu h), _root_.one_mul]
  have := t.semi.smooth
  refine ⟨{ t := t
            proper := hp
            ample := ha
            ktriv := hk
            eta := fun a => I.ev l.M (π • a)
            eta_add := fun a c => by rw [smul_add, I.add]
            eta_ker := fun a h => (I.ker _ hM _).2 (exists_smul_eq ((mul_comm _ _).trans l.prod) hπ h)
            etaA := fun _ => 1
            etaA_add := fun _ _ => (_root_.mul_one _).symm
            etaA_ker := fun _ => rfl
            geom := fun K _ _ x β hx => ?_ }, LevelTwist.sabMapId t, fun a h => ?_⟩
  · obtain ⟨φ, rfl⟩ : ∃ φ : k →+* K, x = spMap φ := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
    obtain rfl : φ.comp σ = β :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective ((Spec.map_comp _ _).trans hx))
    have : CharZero K := charZero_of_injective_ringHom φ.injective
    let J : TateIso D K (Over.mk (spMap φ) ⟶ t.G) (fun a x => x ≫ t.act.act a)
        (fun n x y c => Out.WeilIs t.G t.PP.L n x y (unitOn c)) :=
      tateExtend φ I (MonoidHom.mk' (fun z => toUnit (Over.mk (spMap φ)) ≫ z) fun _ _ => MonObj.comp_mul _ _ _)
        (HeckePoint.toUnit_comp_injective _ _)
        (fun n hn y hy => HeckePoint.exists_of_torsion hL.mulN (HeckePoint.polOf t hp ha hk hg) _
          (Nat.cast_ne_zero.2 hn.ne') (Nat.cast_ne_zero.2 hn.ne') y hy)
        (fun a z => (Category.assoc (toUnit _) z _).symm) (fun n y z c h => by
          have := CommPairing.weilIs_pull hL.globalFns (HeckePoint.isAbelianScheme_of_proper t hp) t.PP.isLB
            (toUnit (Over.mk (spMap φ))) h
          rw [Over.toUnit_left] at this
          rw [← unitOn_map]
          exact this)
    refine ⟨LieExt.detCond_extend D φ t.G t.act hdet, J, ?_, fun a => ?_, fun a h => ?_⟩
    · have h₁ := J.ζ_prim _ l.A_pos
      have h₂ := b.ζ_prim
      rw [hA, IsPrimitiveRoot.one_right_iff] at h₁ h₂
      rw [hA, h₁, h₂, map_one, Units.val_one]
    · rw [hA, MonObj.comp_one]
      exact ((J.ker 1 one_pos a).2 ⟨a, (one_smul _ _).symm⟩).symm
    · exact congrArg (toUnit (Over.mk (spMap φ)) ≫ ·) (hη a h)
  · exact (Category.comp_id _).trans (congrArg (fun q => q.left) (hη a h).symm)

theorem exists_obj_of_uniformised : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (l : Level H) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P' : D'.La →+ (Fin g → ℂ)) (t : SAB H (Sp ℂ)) (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t.G)) (f : ℕ → D.La →ₗ[𝓞 E] D'.La), l.A = 1 → σ (baseKA l).ρ = H.rt0 → D'.p = D.p → D'.q = D.q → IsPeriod D' ty P' → (IsProper t.G.hom ∧ SmoothOfRelativeDimension g t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L ∧ DetCond D' t.act (𝟙 (Sp ℂ)) H.rt0 ∧ (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ (∀ z, e z = 1 ↔ z ∈ P'.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P' a)) (e ((k : ℂ)⁻¹ • P' b)) (unitOn c)) → (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) → (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - D.EF a a') → ∃ (o : Obj D l (baseKA l) (spMap σ)) (m : SABMap t o.t (𝟙 _)), ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), (e ((l.M : ℂ)⁻¹ • P' (f l.M a))).left ≫ m.φ = (o.eta a).left := by
  intro hL E _ _ _ H D D' l σ g ty P' t e f hA hσ hp hq hP ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, _, hw⟩ ⟨htow, hbij⟩ hiso
  have hd : DetCond D t.act (𝟙 (Sp ℂ)) (σ (baseKA l).ρ) := fun τ => by
    rw [hσ, ← hp, ← hq]
    exact h₅ τ
  obtain ⟨I, hI⟩ := exists_tateIso D D' ty P' (fun a x => x ≫ t.act.act a)
    (fun n x y c => Out.WeilIs t.G t.PP.L n x y (unitOn c)) e f hP.1 hP.2.1 h₆ h₇ h₈ h₉ (fun k a b c hk hc => by have := hw k a b c hk hc; beta_reduce; exact this) htow hbij hiso
  obtain ⟨o, m, h⟩ := exists_obj hL hA (baseKA l) σ t h₁ h₂ h₃ h₄ hd I
  refine ⟨o, m, fun a ha => ?_⟩
  exact (congrArg (fun q => q.left ≫ m.φ) (hI l.M a).symm).trans (h a ha)

end GlobalTheory.UnifObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSymmetricInterpolating
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.PointInterp

variable {k : Type} [Field k] {X Y : Scheme.{0}}

def valueAt (p : Spec (CommRingCat.of k) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) : Γ(X, U) →+* k :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.comp (p.appLE U ⊤ h).hom

theorem top_le_iff (p : Spec (CommRingCat.of k) ⟶ X) (U : X.Opens) (z : Spec (CommRingCat.of k)) :
    ⊤ ≤ p ⁻¹ᵁ U ↔ p z ∈ U :=
  ⟨fun h => h (show z ∈ (⊤ : (Spec (CommRingCat.of k)).Opens) from trivial), fun h y _ => by
    obtain rfl : y = z := Subsingleton.elim (α := PrimeSpectrum k) _ _
    exact h⟩

theorem valueAt_rs (p : Spec (CommRingCat.of k) ⟶ X) {U V : X.Opens} (hle : V ≤ U) (h : ⊤ ≤ p ⁻¹ᵁ V)
    (h' : ⊤ ≤ p ⁻¹ᵁ U) (a : Γ(X, U)) : valueAt p V h (rs X hle a) = valueAt p U h' a :=
  congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom (BoxSection.appLE_res p hle h h' a)

theorem valueAt_cst (f : X ⟶ Spec (CommRingCat.of k)) (p : Spec (CommRingCat.of k) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (c : k) : valueAt p U h (cst f U c) = c := by
  refine (valueAt_rs p le_top h le_top _).trans ?_
  have e : p.appLE ⊤ ⊤ le_top = p.appTop := Scheme.Hom.appLE_eq_app p
  have e' : f.appTop ≫ p.appTop = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, hp, Scheme.Hom.id_appTop]
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (f.appTop ≫ p.appLE ⊤ ⊤ le_top) ≫
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom c = c
  rw [e, e', Category.id_comp, Iso.inv_hom_id]
  rfl

theorem valueAt_ne_zero_iff (p : Spec (CommRingCat.of k) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (a : Γ(X, U)) :
    valueAt p U h a ≠ 0 ↔ ⊤ ≤ p ⁻¹ᵁ X.basicOpen a := by
  have hb := Scheme.basicOpen_appLE p ⊤ U h a
  rw [top_inf_eq] at hb
  rw [← hb, ← isUnit_iff_ne_zero]
  constructor
  · intro hu
    have hu' := hu.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    have : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (valueAt p U h a) = (p.appLE U ⊤ h).hom a :=
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id_apply _
    rw [this] at hu'
    exact (Scheme.basicOpen_of_isUnit _ hu').ge
  · intro hu
    refine IsUnit.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom ?_
    exact (Spec (CommRingCat.of k)).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy =>
      (Scheme.mem_basicOpen _ _ y hy).1 (hu hy)

theorem eq_of_valueAt_eq (p q : Spec (CommRingCat.of k) ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    (hp : ⊤ ≤ p ⁻¹ᵁ U) (hq : ⊤ ≤ q ⁻¹ᵁ U) (h : valueAt p U hp = valueAt q U hq) : p = q := by
  have e : p.appLE U ⊤ hp = q.appLE U ⊤ hq := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of k)).hom]
    exact CommRingCat.hom_ext h
  have hV := isAffineOpen_top (Spec (CommRingCat.of k))
  have : IsIso hV.fromSpec := by rw [IsAffineOpen.fromSpec_top]; infer_instance
  rw [← cancel_epi hV.fromSpec, ← hU.SpecMap_appLE_fromSpec p hV hp, ← hU.SpecMap_appLE_fromSpec q hV hq, e]

def subMulSec (f : X ⟶ Spec (CommRingCat.of k)) {H : LB X} (s t : LB.Sec H) (c : k) : LB.Sec H where
  f j := s.f j - cst f _ c * t.f j
  compat i j := by
    rw [map_sub, map_sub, map_mul, map_mul, s.compat i j, t.compat i j]
    have e₁ := rs_cst f (inf_le_left : H.U i ⊓ H.U j ≤ H.U i) c
    have e₂ := rs_cst f (inf_le_right : H.U i ⊓ H.U j ≤ H.U j) c
    rw [e₁, e₂]
    ring

theorem top_le_nonzeroLocus_iff {H : LB X} (s : LB.Sec H) (p : Spec (CommRingCat.of k) ⟶ X) (l : H.ι)
    (hl : ⊤ ≤ p ⁻¹ᵁ H.U l) : ⊤ ≤ p ⁻¹ᵁ nonzeroLocus s ↔ valueAt p _ hl (s.f l) ≠ 0 := by
  let z : Spec (CommRingCat.of k) := (default : PrimeSpectrum k)
  rw [valueAt_ne_zero_iff, top_le_iff _ _ z, top_le_iff _ _ z]
  exact mem_nonzeroLocus_iff_mem_basicOpen_chart s l ((top_le_iff _ _ z).1 hl)

theorem exists_separating (f : X ⟶ Spec (CommRingCat.of k)) {H : LB X} (hH : H.IsLB) {n : ℕ}
    {s : Fin (n + 1) → LB.Sec H} (hs : VeryAmpleBy f H s) (p q : Spec (CommRingCat.of k) ⟶ X)
    (hp : p ≫ f = 𝟙 _) (hq : q ≫ f = 𝟙 _) (hne : p ≠ q) :
    ∃ σ : LB.Sec H, ⊤ ≤ p ⁻¹ᵁ nonzeroLocus σ ∧ ¬ ⊤ ≤ q ⁻¹ᵁ nonzeroLocus σ := by
  let z : Spec (CommRingCat.of k) := (default : PrimeSpectrum k)
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show p z ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)
  have hpa := (top_le_iff p _ z).2 ha
  by_cases hqa : ⊤ ≤ q ⁻¹ᵁ nonzeroLocus (s a)
  swap
  · exact ⟨s a, hpa, hqa⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs.2 a
  obtain ⟨b, hb⟩ : ∃ b, valueAt p _ hpa (r b) ≠ valueAt q _ hqa (r b) := by
    by_contra hc
    push_neg at hc
    refine hne (eq_of_valueAt_eq p q haff hpa hqa (RingHom.ext fun x => ?_))
    obtain ⟨F, rfl⟩ := hsurj x
    induction F using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.eval₂Hom_C, valueAt_cst f p hp, valueAt_cst f q hq]
    | add F G hF hG => rw [map_add, map_add, map_add, hF, hG]
    | mul_X F j hF => rw [map_mul, MvPolynomial.eval₂Hom_X', map_mul, map_mul, hF, hc]
  have key : ∀ (x : Spec (CommRingCat.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (hxa : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (s a)) (c : k),
      ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (subMulSec f (s b) (s a) c) ↔ valueAt x _ hxa (r b) ≠ c := by
    intro x hx hxa c
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show x z ∈ ⨆ i, H.U i by rw [hH.cover]; trivial)
    have hxl := (top_le_iff x _ z).2 hl
    have hm : ⊤ ≤ x ⁻¹ᵁ (nonzeroLocus (s a) ⊓ H.U l) := le_inf hxa hxl
    have e := congrArg (valueAt x _ hm) (hr b l)
    rw [map_mul, valueAt_rs x _ hm hxl, valueAt_rs x _ hm hxl, valueAt_rs x _ hm hxa] at e
    have h0 := (top_le_nonzeroLocus_iff (s a) x l hxl).1 hxa
    rw [top_le_nonzeroLocus_iff _ x l hxl]
    change valueAt x _ hxl ((s b).f l - cst f _ c * (s a).f l) ≠ 0 ↔ _
    rw [map_sub, map_mul, valueAt_cst f x hx, e, ← sub_mul, mul_ne_zero_iff, sub_ne_zero]
    exact and_iff_left h0
  exact ⟨subMulSec f (s b) (s a) (valueAt q _ hqa (r b)), (key p hp hpa _).2 hb,
    fun h => (key q hq hqa _).1 h rfl⟩

theorem mem_nonzeroLocus_of_prodSec (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (t : K → L.Sec)
    (y : Y) (h : y ∈ nonzeroLocus (BoxSection.prodSec L φ t)) (i : K) : φ i y ∈ nonzeroLocus (t i) := by
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  have hy : y ∈ LB.wchart L φ l := Y.basicOpen_le _ hl
  have h₁ := (mem_basicOpen_finset_prod_iff _ Finset.univ hy).1 hl i (Finset.mem_univ i)
  exact TopologicalSpace.Opens.mem_iSup.2
    ⟨l i, ((Scheme.basicOpen_appLE (φ i) _ _ (LB.wchart_le L φ l i) _).le h₁).2⟩

theorem exists_symmetric_interpolating : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → IsProjBy A.hom → ∃ L : LB A.left, L.IsLB ∧ Triv (LB.LinComb L (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1]) ∧ ∀ (r : ℕ) (p : Fin r → (𝟙_ (Over (Sp k)) ⟶ A)), Function.Injective p → ∀ m : ℕ, r ≤ m → ∃ s : Fin r → LB.Sec (pw L m), ∀ i j, (⊤ ≤ (p j).left ⁻¹ᵁ nonzeroLocus (s i) ↔ i = j) := by
  intro k _ _ A _ _ ⟨H, hH, n, s, hs⟩
  let φ : Fin 2 → (A.left ⟶ A.left) := ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left]
  have hL : (LB.LinComb H φ (fun _ => 1)).IsLB := LB.isLB_linComb hH _ _
  refine ⟨LB.LinComb H φ (fun _ => 1), hL, ?_, fun r p hp m hm => ?_⟩
  · refine PrimNorm.hasGen_nested hH φ _ _ _ ?_
    have e : (GrpObj.inv : A ⟶ A).left ≫ (GrpObj.inv : A ⟶ A).left = 𝟙 A.left := by
      rw [← Over.comp_left, GrpObj.inv_comp_inv, Over.id_left]
    simp only [Fin.prod_univ_two, φ, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, e,
      Category.id_comp, zpow_one, zpow_neg]
    rw [mul_comm (PrimNorm.cls H (𝟙 A.left)), mul_inv_cancel]
  · let z : Spec (CommRingCat.of k) := (default : PrimeSpectrum k)
    let P : Fin r → (Spec (CommRingCat.of k) ⟶ A.left) := fun i => (p i).left
    have hP : ∀ i, P i ≫ A.hom = 𝟙 _ := fun i => Over.w (p i)
    have hcov : ∀ x : A.left, ∃ σ : LB.Sec H, x ∈ nonzeroLocus σ := fun x => by
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1
        (show x ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)
      exact ⟨s a, ha⟩

    have hsep : ∀ (i : Fin r) (t : Fin m), ∃ σ : LB.Sec H, P i z ∈ nonzeroLocus σ ∧
        ∀ j : Fin r, (j : ℕ) = t → i ≠ j → P j z ∉ nonzeroLocus σ := fun i t => by
      by_cases h : ∃ j : Fin r, (j : ℕ) = t ∧ i ≠ j
      · obtain ⟨j, hj, hij⟩ := h
        obtain ⟨σ, h₁, h₂⟩ := exists_separating A.hom hH hs (P i) (P j) (hP i) (hP j)
          fun e => hij (hp (Over.OverMorphism.ext e))
        refine ⟨σ, (top_le_iff _ _ z).1 h₁, fun j' hj' _ h => ?_⟩
        obtain rfl : j' = j := Fin.ext (hj'.trans hj.symm)
        exact h₂ ((top_le_iff _ _ z).2 h)
      · obtain ⟨σ, hσ⟩ := hcov (P i z)
        exact ⟨σ, hσ, fun j hj hij _ => h ⟨j, hj, hij⟩⟩
    choose σ hσ hσ' using hsep
    choose τ hτ using fun i => hcov (φ 1 (P i z))
    have hprod : ∀ i : Fin r, ∃ u : LB.Sec (pw (LB.LinComb H φ (fun _ => 1)) m),
        nonzeroLocus u = ⨅ t ∈ (Finset.univ : Finset (Fin m)),
          nonzeroLocus (BoxSection.prodSec H φ ![σ i t, τ i]) := fun i => by
      have h := exists_prod_sec_nonzeroLocus _ _ _ (fun t => BoxSection.prodSec H φ ![σ i t, τ i])
        (Finset.univ : Finset (Fin m)) hL
      obtain ⟨u, -, hu⟩ := h
      have hc : ((Finset.univ : Finset (Fin m)).card : ℤ) = (m : ℤ) := by simp
      revert u
      rw [hc]
      exact fun u hu => ⟨u, hu⟩
    choose u hu using hprod
    refine ⟨u, fun i j => ?_⟩
    refine (top_le_iff (P j) _ z).trans ?_
    rw [hu, mem_finset_biInf_opens_iff]
    constructor
    · intro h
      by_contra hij
      exact hσ' i ⟨j, j.2.trans_le hm⟩ j rfl hij
        (mem_nonzeroLocus_of_prodSec H φ _ _ (h ⟨j, j.2.trans_le hm⟩ (Finset.mem_univ _)) 0)
    · rintro rfl t -
      refine BoxSection.mem_nonzeroLocus_prodSec H φ _ _ fun l => ?_
      fin_cases l
      exacts [hσ i t, hτ i]

end GlobalTheory.PointInterp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LandherrSelfDual
section
theorem GlobalTheory.SelfDualIsom.landherrSelfDual : Formalism.L2.Pj.LandherrSelfDual := by
  unfold Formalism.L2.Pj.LandherrSelfDual
  exact GlobalTheory.SelfDualIsom.exists_scaled_isometry GlobalTheory.QNorm.hasseNormSt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemPrincipalCongruenceInterCuspCentreIffStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_principalCongruence_inter_cuspCentre_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (r ρ : ℕ) (X : Data E r) (N : ℕ) (D : Datum H) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), LinearMap.range φ = X.Λ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (X.Gm a b) = X.Gm b a) ∧ X.Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ x) (φ y))) → (∀ γ : GL (Fin r) E, γ ∈ X.Γ ↔ IsUStab X.Gm X.Λ γ ∧ ∀ v ∈ X.Λ, ∃ w ∈ X.Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + N • w) → (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) → ∀ β, β ∈ FJ.zGam X cu ↔ FJ.IsSkew β ∧ ∀ a b (y : E), (∀ a' ∈ cc' b, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) → ∃ z ∈ cc' a, β a b / X.ξ0 * y = (N : E) * z := by
  first | exact @GlobalTheory.CuspCentre.mem_zGam_principal_iff | exact GlobalTheory.CuspCentre.mem_zGam_principal_iff | (intros; apply GlobalTheory.CuspCentre.mem_zGam_principal_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedPointsSatisfySingleFrameStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalised_points_satisfy_single_frame : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k) (un : (M.X k).dom → FrPt Xo c (CAt σ)), GoodEmb c σ → ModelBase M → NegXi M → IsNormUn T un → ∀ x, FrameOK e F M k x (un x) := by
  first | exact @GlobalTheory.NormFrame.frameOK_of_isNormUn | exact GlobalTheory.NormFrame.frameOK_of_isNormUn | (intros; apply GlobalTheory.NormFrame.frameOK_of_isNormUn <;> assumption)
end

