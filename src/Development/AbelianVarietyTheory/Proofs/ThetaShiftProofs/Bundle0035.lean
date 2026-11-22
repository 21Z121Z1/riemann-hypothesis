import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0030
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0033

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcInPlace
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.ArcPlace

open HostModel ToricData ConjDual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

def restrict {D : Datum H} {c : Coeff l} {O k : Type} [CommRing O] [CommRing k] [IsDomain k] (β : O →+* c.F)
    {bF : c.F →+* k} (a : ArcIn D l (RingHom.id c.F) k bF) : ArcIn D l β k (bF.comp β) where
  D₀ := a.D₀
  mod := a.mod
  oa := a.oa
  nontriv := a.nontriv
  even := a.even
  bimult := a.bimult
  gen := a.gen
  w0 := a.w0
  be := a.be
  be_symm := a.be_symm
  be_pos := a.be_pos
  be_adj := a.be_adj
  be_dvd := a.be_dvd
  eta := a.eta
  etaA := a.etaA
  geom F _ _ _ r z := a.geom F (β r) (β z)

variable (c : Coeff l) {F₁ : Type} [Field F₁] (g : c.F →+* F₁)

def root {a : ℕ} (h : a ∣ l.M') : F₁ˣ :=
  Units.map g.toMonoidHom
    (Units.mk0 ⟨zeta a, zeta_mem_coeff_of_dvd c h⟩ fun e => Complex.exp_ne_zero _ (congrArg Subtype.val e))

theorem root_pow {a : ℕ} (h : a ∣ l.M') : root c g h ^ a = 1 := by
  have h1 : IsPrimitiveRoot (⟨zeta a, zeta_mem_coeff_of_dvd c h⟩ : c.F) a :=
    IsPrimitiveRoot.of_map_of_injective (f := c.F.val)
      (isPrimitiveRoot_zeta (Nat.pos_of_dvd_of_pos h (LevelExist.M'_pos l))) Subtype.val_injective
  exact Units.ext (h1.map_of_injective g.injective).pow_eq_one

def arcInFrac {O k : Type} [CommRing O] [CommRing k] [IsDomain k] (β : O →+* c.F) (b : O →+* k)
    (g : c.F →+* FractionRing k) (hg : ∀ x, g (β x) = algebraMap k _ (b x)) : ArcIn (hypDatum H) l β k b where
  D₀ := toricPre k (𝓞 E) fun _ => 1
  oa := arcAct H k
  nontriv := inferInstanceAs (Nontrivial (𝓞 E))
  even := psiEven _ fun _ => rfl
  bimult := tauBimult _ fun _ _ _ => by simp [polar_one]
  gen y := psiUnitOn _ y 1 (by simp)
  w0 := letI := H.starRing; psi_weight_zero_linear_combination _ (𝓞 E) (polar_one_smul k) H.w0 fun _ => polar_one k _ _
  be := arcForm l
  be_symm (y z : 𝓞 E) := congrArg ((2 * l.M' : ℤ) * ·) (trForm_symm H y z)
  be_pos (y : 𝓞 E) hy := mul_pos (mul_pos two_pos (Int.natCast_pos.2 (LevelExist.M'_pos l))) (trForm_pos H hy)
  be_adj a (y z : 𝓞 E) := congrArg ((2 * l.M' : ℤ) * ·) (trForm_adj H a y z)
  be_dvd (y z : 𝓞 E) := ⟨trForm H y z, rfl⟩
  eta := qkPt k (root c g (Nat.dvd_lcm_left l.M l.A)) (root_pow c g _)
  etaA := qkPt k (root c g (Nat.dvd_lcm_right l.M l.A)) (root_pow c g _)
  geom := by
    letI := H.starRing
    intro F _ _ _ r z _ hz f hf
    refine ⟨fun τ => ⟨0, lieMult_zero _ (𝓞 E) (polar_one_smul k) f τ, ?_⟩, ?_⟩
    · rw [hypDatum_p, hypDatum_q, ite_self, zero_add]
      exact Module.finrank_self (𝓞 E)
    haveI := c.fin
    obtain ⟨ζ, hp, hc, hζ⟩ := exists_roots c.F F ((algebraMap (FractionRing k) F).comp g)
    have key : ∀ {n : ℕ} (h : n ∣ l.M') (a : HypLattice H) q,
        QkExt (algebraMap _ F) (qkPt k (root c g h) (root_pow c g h) a) q →
          Out.QkPt.Equiv _ F q ((tateIsoQ H k ζ hp hc).ev n a) := fun {n} h a q hq => by
      rw [qkExt_qkPt k _ (algebraMap (FractionRing k) F) (RingHom.ext fun _ => rfl) (pow_eq_one_of_prim hp n)
        (hζ n (Nat.pos_of_dvd_of_pos h (LevelExist.M'_pos l)) ⟨zeta n, zeta_mem_coeff_of_dvd c h⟩ rfl)] at hq
      subst hq
      exact equiv_refl_split k F _
    refine ⟨tateIsoQ H k ζ hp hc, (hζ l.A l.A_pos (β z) hz).trans ?_, key _, fun a _ => key _ a⟩
    rw [hf, RingHom.comp_apply, hg]
    rfl

end GlobalTheory.ArcPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmpCongrOfExEq
section
noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem cmp_congr_of_ex_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) ty P) (k : ℕ) (hk : 0 < k) (a b : (Fu.Di i).La)
    (hab : Fu.ex i P ((k : ℂ)⁻¹ • P a) = Fu.ex i P ((k : ℂ)⁻¹ • P b)) : ∃ e, a = b + k • e := by
  have h1 : Fu.ex i P ((k : ℂ)⁻¹ • P a - (k : ℂ)⁻¹ • P b) = 1 := by
    have h2 := Fu.ex_add i P hP ((k : ℂ)⁻¹ • P a - (k : ℂ)⁻¹ • P b) ((k : ℂ)⁻¹ • P b)
    rw [sub_add_cancel, hab] at h2
    exact mul_eq_right.1 h2.symm
  obtain ⟨e, he⟩ := (Fu.ex_ker i P hP _).1 h1
  refine ⟨e, hP.2.1 ?_⟩
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [map_add, map_nsmul, he, ← Nat.cast_smul_eq_nsmul ℂ, smul_sub, smul_inv_smul₀ hk', smul_inv_smul₀ hk']
  abel

theorem cmp_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
    (A : AnArc (𝓞 E)) (w : ℂ) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) ty P) (y₀ : Sp ℂ ⟶ Xo.X) (hy : Fu.u i P = y₀)
    (π : A.V → (Over.mk y₀ ⟶ Xo.univ.t.G)) (h : A.V ≃L[ℂ] (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La)
    (hex : ∀ v, (Fu.ex i P (h v)).left = (π v).left) (hPg : ∀ u, P u = h (A.Pw w (gam u)))
    (k : ℕ) (hk : 0 < k) (x : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (a : (Fu.Di i).La) (la : A.La)
    (h1 : toUnit _ ≫ x = Fu.ex i P ((k : ℂ)⁻¹ • P a)) (h2 : toUnit _ ≫ x = π ((k : ℂ)⁻¹ • A.Pw w la)) :
    ∃ e, gam a = la + k • e := by
  subst hy
  have h3 : ∀ v, Fu.ex i P (h v) = π v := fun v => Over.OverMorphism.ext (hex v)
  obtain ⟨e, he⟩ := cmp_congr_of_ex_eq Fu i P hP k hk a (gam.symm la) (by
    rw [← h1, h2, ← h3, map_smul, hPg (gam.symm la), gam.apply_symm_apply])
  exact ⟨gam e, by rw [he, map_add, map_nsmul, gam.apply_symm_apply]⟩

theorem exists_cmp : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (A : AnArc (𝓞 E)) (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ) (T : ℝ) (yw : ℂ → (Sp ℂ ⟶ Xo.X)) (π : ∀ w, A.V → (Over.mk (yw w) ⟶ Xo.univ.t.G)) (fr : ℂ → Xo.univ.t.PP.L.ι → A.V → ℂ) (laA laM : D.La → A.La), (inferInstance : StarRing (𝓞 E)) = H.starRing → (∀ w la la', lin w la (A.Pw w la') - lin w la' (A.Pw w la) = -(2 * Real.pi * Complex.I) * A.EF la la') → Module.finrank ℂ A.V = g → IsHolTo {w : ℂ | T < w.im} yw → (∀ w : ℂ, T < w.im → yw w ≫ Xo.s = spMap σ ∧ IsFibAt A Xo.univ.t lin cst w (yw w) (π w) (fr w) ∧ (Function.Surjective (π w) → (∀ v, toUnit _ ≫ Xo.univ.etaA v = π w ((l.A : ℂ)⁻¹ • A.Pw w (laA v))) ∧ ∀ v ∈ idealPart D l, toUnit _ ≫ Xo.univ.eta v = π w ((l.M : ℂ)⁻¹ • A.Pw w (laM v)))) → ∃ K : Cmp Fu A yw π laA laM, T ≤ K.T := by
  intro hL hL2 E _ _ _ H _ D l Xo σ g ty Fu A lin cst T yw π fr laA laM hstar hlin hrk hhol hw
  obtain ⟨i, hi⟩ := GlobalTheory.familyUnif_component_const E H D l Xo σ g ty Fu T yw hhol fun w h => (hw w h).1
  obtain ⟨T₀, hT₀⟩ := GlobalTheory.fibre_comparison hL hL2 E H D l Xo σ g ty Fu A lin cst hlin hrk
  obtain ⟨T₁, hT₁⟩ := A.exists_BwMat_posDef
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le

  have key : ∀ w : ℂ, max T (max T₀ T₁) < w.im →
      ∃ (P : (Fu.Di i).La →+ (Fin g → ℂ)) (h : A.V ≃L[ℂ] (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La),
        IsPeriod (Fu.Di i) ty P ∧ Fu.u i P = yw w ∧ (∀ v, (Fu.ex i P (h v)).left = (π w v).left) ∧
        (∀ u, P u = h (A.Pw w (gam u))) ∧ (∀ u v, A.EF (gam u) (gam v) = (Fu.Di i).EF u v) ∧
        (∀ (e : 𝓞 E) v k, h (A.actV e v) k = ty k (e : E) * h v k) ∧
        (∀ v, ∃ e, gam (Fu.t i v) = laA v + l.A • e) ∧
        ∀ v ∈ idealPart D l, ∃ e, gam (Fu.t i v) = laM v + l.M • e := by
    intro w hwT
    have h1 : T < w.im := lt_of_le_of_lt (le_max_left _ _) hwT
    have h2 : T₀ < w.im := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hwT
    obtain ⟨P, hP, hu⟩ := hi w h1
    obtain ⟨-, hfib, hlev⟩ := hw w h1
    obtain ⟨hs, h, gam, hex, hPg, hEF, hact⟩ := hT₀ w i P (yw w) (π w) (fr w) h2 hP hu hfib
    obtain ⟨hA, hMM⟩ := hlev hs
    exact ⟨P, h, gam, hP, hu, hex, hPg, hEF, hact,
      fun v => cmp_level Fu A w i P hP _ hu (π w) h gam hex hPg l.A l.A_pos _ _ _ (Fu.ex_etaA i P hP v) (hA v),
      fun v hv => cmp_level Fu A w i P hP _ hu (π w) h gam hex hPg l.M hM _ _ _ (Fu.ex_eta i P hP v hv) (hMM v hv)⟩
  obtain ⟨-, h₁, gam₁, -, -, -, -, hEF₁, hact₁, hA₁, hM₁⟩ :=
    key (((max T (max T₀ T₁) + 1 : ℝ) : ℂ) * Complex.I) (by simp)
  let Pw : ℂ → ((Fu.Di i).La →+ (Fin g → ℂ)) := fun w =>
    (h₁.toLinearEquiv.toLinearMap.toAddMonoidHom.comp (A.Pw w)).comp gam₁.toLinearMap.toAddMonoidHom
  have hPw : ∀ w u, Pw w u = h₁ (A.Pw w (gam₁ u)) := fun _ _ => rfl
  have hper : ∀ w : ℂ, max T (max T₀ T₁) < w.im → IsPeriod (Fu.Di i) ty (Pw w) := fun w hwT =>
    A.isPeriod (hT₁ w (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hwT)) (Fu.Di i) ty
      h₁.toLinearEquiv hact₁ gam₁.toAddEquiv (fun a x => gam₁.map_smul a x) hEF₁ (Pw w) (hPw w)
  have hmod : ∀ (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La) (k : ℕ) (a : (Fu.Di i).La) (la : A.La),
      (∃ e, gam a = la + k • e) → (∃ e, gam₁ a = la + k • e) → ∃ e, (gam.trans gam₁.symm) a = a + k • e := by
    rintro gam k a la ⟨e, he⟩ ⟨e₁, he₁⟩
    refine ⟨gam₁.symm (e - e₁), gam₁.injective ?_⟩
    rw [LinearEquiv.trans_apply, gam₁.apply_symm_apply, map_add, map_nsmul, gam₁.apply_symm_apply, he, he₁, smul_sub]
    abel
  have hrig : ∀ w : ℂ, max T (max T₀ T₁) < w.im →
      Fu.u i (Pw w) = yw w ∧ ∀ v, (Fu.ex i (Pw w) (h₁ v)).left = (π w v).left := by
    intro w hwT
    obtain ⟨P, h, gam, hP, hu, hex, hPg, hEF, -, hA, hMM⟩ := key w hwT
    obtain ⟨r1, r2⟩ := GlobalTheory.T.exp_eq_of_isometry_matching_markings E H D l Xo σ g ty Fu i P (Pw w) (gam.trans gam₁.symm)
      (h.symm.trans h₁).toLinearEquiv hstar hP (hper w hwT)
      (fun u v => by
        rw [← hEF₁, LinearEquiv.trans_apply, LinearEquiv.trans_apply, gam₁.apply_symm_apply, gam₁.apply_symm_apply, hEF])
      (fun v hv => hmod gam _ _ _ (hMM v hv) (hM₁ v hv)) (fun v => hmod gam _ _ _ (hA v) (hA₁ v))
      (fun u => by rw [hPw, hPg]; simp)
    refine ⟨r1.symm.trans hu, fun v => ?_⟩
    have := r2 (h v)
    rw [hex] at this
    rw [← this]
    simp
  exact ⟨⟨i, max T (max T₀ T₁), gam₁, h₁, hEF₁, hact₁, Pw, hPw, hper, fun w hwT => (hrig w hwT).1,
    fun w hwT => (hrig w hwT).2, hA₁, hM₁⟩, le_max_left _ _⟩

end GlobalTheory.ArcPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantPointFrameIsFrameWithRigidification
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstFrame

theorem valR_g_self {A : Type} [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} {L : LB Z} (hL : L.IsLB) (x : Sp A ⟶ Z)
    (j : L.ι) (h : ⊤ ≤ x ⁻¹ᵁ L.U j) : valR x (L.U j ⊓ L.U j) (L.g j j).val = 1 := by
  apply toStkA_injective
  rw [toStkA_valR x (L.U j ⊓ L.U j) _ (fun _ hz => ⟨h hz, h hz⟩), map_one]
  exact congrArg Units.val (gm_self hL x _ (h trivial))

theorem valR_rig {A A₀ : Type} [CommRing A] [IsLocalRing A] [CommRing A₀] {B : Over (Sp A)} {B₀ : Over (Sp A₀)}
    [GrpObj B] [IsCommMonObj B] [GrpObj B₀] [IsCommMonObj B₀] {M : LB B.left} {M₀ : LB B₀.left} (f : A₀ →+* A)
    {φ : B.left ⟶ B₀.left} (he : eSec B ≫ φ = spMap f ≫ eSec B₀) (w : LB.Iso M (M₀.pull φ))
    (r : LB.Gen (M.pull (eSec B))) (r₀ : LB.Gen (M₀.pull (eSec B₀)))
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec B) (fun _ => 1)) r (rigPullOf φ (spMap f) he M₀ r₀))
    (j : M.ι) (j₀ : M₀.ι) (hj : ⊤ ≤ (show Sp A ⟶ _ from eSec B) ⁻¹ᵁ (LB.div (M₀.pull φ) M).U (fun _ => j₀, j))
    (hj₀ : ⊤ ≤ (M₀.pull (eSec B₀)).U (fun _ => j₀)) :
    f (valR (𝟙 (Sp A₀)) ((M₀.pull (eSec B₀)).U (fun _ => j₀)) (r₀.s (fun _ => j₀)).val) =
      valR (A := A) (eSec B) _ (w.s (fun _ => j₀, j)).val *
        valR (𝟙 (Sp A)) ((M.pull (eSec B)).U (fun _ => j)) (r.s (fun _ => j)).val := by
  have hc := hj (show cpt A ∈ (⊤ : (Sp A).Opens) from trivial)
  have e := gm_maps_pt h (𝟙 (Sp A)) (cpt A) (fun _ => j₀) j hc.1 hc.2
  have hr : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ (M.pull (eSec B)).U (fun _ => j) := fun z hz => mem_pull.2 (hj hz).2
  have h₀ : ⊤ ≤ (𝟙 (Sp A₀)) ⁻¹ᵁ (M₀.pull (eSec B₀)).U (fun _ => j₀) := hj₀
  have h₁ := FormalValue.top_le_comp h₀ (spMap f)
  apply toStkA_injective
  refine Eq.trans ?_ ((congrArg Units.val e).trans ?_)
  · refine (congrArg _ (FormalValue.valR_spMap f _ _ h₀ _).symm).trans ((toStkA_valR _ _ _ h₁ _).trans
      (congrArg Units.val ?_))
    have hm : (𝟙 (Sp A) : Sp A ⟶ Sp A) (cpt A) ∈ ((M₀.pull φ).pull (eSec B)).U (fun _ _ => j₀) := mem_pull.2 hc.1
    refine Eq.trans ?_ ((gm_res (𝟙 (Sp A)) _ _ hm _).trans (gm_pull (𝟙 (Sp A)) (spMap f) _ _ (hj₀ trivial) _)).symm
    rw [Category.id_comp, Category.comp_id]
  · refine Eq.trans ?_ (map_mul _ _ _).symm
    exact (Units.val_mul _ _).trans (congrArg₂ (· * ·) (toStkA_valR (A := A) (eSec B) _ _ hj _).symm
      (toStkA_valR _ _ _ hr _).symm)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}
  {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : GtAn a}
  (Ξ : ConstPts W Λ)

omit [Algebra (FractionRing ℂ) ℂ] in

theorem complete : IsAdicComplete ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ := by
  rw [Algebra.algebraMap_self, Ideal.map_id]
  infer_instance

theorem base_comp (v : Λ.A.V) :
    (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex v.2).left :=
  ((Ξ.g_rel v 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b v))

theorem exists_charts (v : Λ.A.V) : ∃ (jM : W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι),
    ⊤ ≤ (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) ∧
    ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ a.D₀.P.L.U j₀ := by
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) (cpt ℂ⟦X⟧))
  have h₀ := FrameValue.le_chartAt a.D₀.P.isLB (Λ.u.ex v.2).left
  refine ⟨jM, _, (top_le_iff_cpt _ _).2 ⟨mem_pull.2 ?_, hM⟩, h₀⟩
  exact (congrArg (fun q => q (cpt ℂ⟦X⟧) ∈ a.D₀.P.L.U _) (base_comp Ξ v)).mpr (FormalValue.top_le_comp h₀ _ trivial)

theorem isFrm (v : Λ.A.V) : IsFrm W.P.U.LG.L (Ξ.x v).left (Ξ.τ v) := by
  haveI := complete
  obtain ⟨jM, j₀, hj, h₀⟩ := exists_charts Ξ v
  have hw := FormalValue.isUnit_valR (A := ℂ⟦X⟧) (Ξ.g v).b.left _ hj (W.w.s (fun _ => j₀, jM))
  have hM : ⊤ ≤ FormalValue.basePt (Ξ.g v) ⁻¹ᵁ W.P.D.toPre.P.L.U jM := fun z hz => (hj hz).2
  refine ⟨fun j h => ?_, fun j j' h => ?_⟩
  · refine isUnit_of_mul_isUnit_right ((congrArg IsUnit (Ξ.τ_eq v j jM j₀ h hj)).mpr ?_)
    exact (Units.isUnit _).mul ((Ne.isUnit (Λ.u.fr_ne j₀ v.2 h₀)).map _)
  · have h₁ : ⊤ ≤ (Ξ.x v).left ⁻¹ᵁ W.P.U.LG.L.U j := fun z hz => (h hz).1
    have h₂ : ⊤ ≤ (Ξ.x v).left ⁻¹ᵁ W.P.U.LG.L.U j' := fun z hz => (h hz).2
    have t := FormalValue.tau_trans (Ξ.x_fm v) h₁ h₂ hM hM
    rw [valR_g_self W.P.D.toPre.P.isLB _ jM hM, _root_.mul_one] at t
    have e₁ := Ξ.τ_eq v j jM j₀ h₁ hj
    have e₂ := Ξ.τ_eq v j' jM j₀ h₂ hj
    refine hw.mul_left_cancel (e₁.trans ?_)
    refine (congrArg (· * _) t).trans ?_
    rw [_root_.mul_assoc, mul_left_comm]
    exact (mul_left_comm _ _ _).trans ((congrArg (_ * ·) e₂.symm).trans (mul_left_comm _ _ _))

theorem tau_zero (hx : Ξ.x 0 = 1) (j : W.P.U.LG.L.ι) (h : ⊤ ≤ (Ξ.x 0).left ⁻¹ᵁ W.P.U.LG.L.U j) :
    Ξ.τ 0 j = valR (𝟙 (Sp ℂ⟦X⟧)) ((W.P.U.LG.L.pull (eSec W.t.G)).U (fun _ => j))
      (W.P.U.LG.rig.s (fun _ => j)).val := by
  haveI := complete
  have hs : spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = 𝟙 _ := Spec.map_id _
  obtain ⟨jM, j₀, hj, h₀⟩ := exists_charts Ξ 0
  have hw := FormalValue.isUnit_valR (A := ℂ⟦X⟧) (Ξ.g 0).b.left _ hj (W.w.s (fun _ => j₀, jM))
  have hM : ⊤ ≤ FormalValue.basePt (Ξ.g 0) ⁻¹ᵁ W.P.D.toPre.P.L.U jM := fun z hz => (hj hz).2
  have hx' : (Ξ.x 0).left = spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) ≫ eSec W.t.G := by
    refine (congrArg Over.Hom.left hx).trans ?_
    exact congrArg (· ≫ eSec W.t.G) ((Category.comp_id _).symm.trans (Over.w (toUnit selfR)))
  have hu : (Λ.u.ex (0 : Λ.A.V).2).left = eSec a.D₀.P.A := by
    refine (congrArg Over.Hom.left ((Λ.u.ker 0).2 Λ.u.Λ.zero_mem)).trans ?_
    rw [Hom.one_def]; simp [eSec]
  have hb : FormalValue.basePt (Ξ.g 0) = eSec W.P.D.toPre.P.A := by
    refine W.spec.1.1.hom_ext ?_ ?_
    · exact (base_comp Ξ 0).trans ((congrArg (_ ≫ ·) hu).trans W.he.symm)
    · exact (Over.w (Ξ.g 0).b).trans (hs.trans (Over.w η[W.P.D.toPre.P.A]).symm)
  have hb' : FormalValue.basePt (Ξ.g 0) = spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) ≫ eSec W.P.D.toPre.P.A :=
    hb.trans ((Category.id_comp _).symm.trans (congrArg (· ≫ _) hs.symm))
  have hf := Ξ.x_fm 0
  have e := Ξ.τ_eq 0 j jM j₀ h hj
  rw [hx'] at hf h e
  have t := FormalValue.tau_rig hf hb' h hM
  have hj₀ : ⊤ ≤ (a.D₀.P.L.pull (eSec a.D₀.P.A)).U (fun _ => j₀) := fun z hz =>
    mem_pull.2 ((congrArg (fun q => q z ∈ a.D₀.P.L.U j₀) hu).mp (h₀ hz))
  have r := valR_rig (PowerSeries.C (R := ℂ)) W.he W.w W.P.D.toPre.rig a.D₀.rig W.spec.2.2.1 jM j₀ (hb ▸ hj) hj₀
  have f := (congrArg (PowerSeries.C (R := ℂ)) (Λ.rig (fun _ => j₀) hj₀)).trans r
  replace f := f.trans (congrArg (fun q => valR (A := ℂ⟦X⟧) q _ (W.w.s (fun _ => j₀, jM)).val * _) hb.symm)
  refine hw.mul_left_cancel (e.trans ((congrArg (_ * ·) f).trans ((mul_left_comm _ _ _).trans (congrArg (_ * ·) ?_))))
  have t' := t
  generalize FormalValue.tau W.P.U.toUnifPre ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧))
    (spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) ≫ eSec W.t.G) j jM = q at t' ⊢
  rw [hs] at t'
  exact t'

omit [Algebra (FractionRing ℂ) ℂ] in

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) , (∀ v, IsFrm W.P.U.LG.L (Ξ.x v).left (Ξ.τ v)) ∧ ∀ j, ⊤ ≤ (Ξ.x 0).left ⁻¹ᵁ W.P.U.LG.L.U j → Ξ.τ 0 j = valR (𝟙 (Sp ℂ⟦X⟧)) ((W.P.U.LG.L.pull (eSec W.t.G)).U (fun _ => j)) (W.P.U.LG.rig.s (fun _ => j)).val := by
  intro h₁ h₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ
  refine ⟨isFrm Ξ, tau_zero Ξ ?_⟩
  have h := (GlobalTheory.ArcPts.constPts_add_smul h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ).1 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

end GlobalTheory.ConstFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantSectionMulCoordDualNumberPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantSection_mul_coord_dualNumberPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)) (j : ℕ) (x : a.D₀.X) (s₀ : a.D₀.SecB j x) (f : W.P.D.toPre.SecB j (W.e x)) (r : ℂ⟦X⟧) (jM : W.P.D.toPre.P.L.ι) (jf jt : Fin 4 → W.P.D.toPre.P.L.ι) (jt₀ : Fin 4 → a.D₀.P.L.ι), TanRel W ν g₁ → IsConstMul W j x s₀ f r → FormalValue.CohCharts g₁ (W.e x) jM jf jt → ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) jt₀ → valR (A := DualNumber ℂ⟦X⟧) g₁.b.left _ (W.w.s (fun _ => jt₀ 2, jM)).val ^ j * (FormalValue.famVal g₁ f jf * FormalValue.coordVal g₁ (W.e x) jt) = TrivSqZeroExt.inl r * constEps (valR (A := DualNumber ℂ) ν.b.left (LB.wchart a.D₀.P.L (a.D₀.famφB x) ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) (s₀.f ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) * valR (A := DualNumber ℂ) (𝟙 _) (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) jt₀) ((ν.s x).s jt₀).val) := by
  first | exact @GlobalTheory.ConstTanAlg.main | exact GlobalTheory.ConstTanAlg.main | (intros; apply GlobalTheory.ConstTanAlg.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTangentEqFormalPointTransportedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantTangent_eq_formalPoint_transported : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (g : ℕ) (ex₀ : (Fin g → ℂ) → Out.GtPtF a.D₀ ℂ) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR ℂ⟦X⟧ ⟶ W.t.G) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)), DiffHyp W ex₀ z₀ ν v → TanRel W ν g₁ → FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v.left := by
  first | exact @GlobalTheory.ConstTanFormal.main | exact GlobalTheory.ConstTanFormal.main | (intros; apply GlobalTheory.ConstTanFormal.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTangentReductionEqOriginStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantTangent_reduction_eq_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (Ξ : ConstPts W Λ) (v : epsR ℂ⟦X⟧ ⟶ W.t.G) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)), DiffHyp W (fun z => Λ.ex0 (h.symm z)) z₀ ν v → TanRel W ν g₁ → FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v.left → spMap (TrivSqZeroExt.fstHom ℂ⟦X⟧ ℂ⟦X⟧ ℂ⟦X⟧).toRingHom ≫ v.left = (Ξ.x 0).left := by
  first | exact @GlobalTheory.ConstTanRed.main | exact GlobalTheory.ConstTanRed.main | (intros; apply GlobalTheory.ConstTanRed.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantTorusExtensionTangentRelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constantTorusExtension_tangentRel : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (ν : Out.GtPt a.D₀ (epsR ℂ)), ∃ g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧), TanRel W ν g₁ := by
  first | exact @GlobalTheory.ConstTan.exists_tanRel | exact GlobalTheory.ConstTan.exists_tanRel | (intros; apply GlobalTheory.ConstTan.exists_tanRel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLatticeVectorRepAndShiftStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeVector_rep_and_shift : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (k : ℕ), 1 ≤ k → (∀ p, ∃ la, Λ.Rep k p la) ∧ ∀ p la e, Λ.Rep k p la → ∃ q : Out.QkPt a.D₀ ℂ k, q.y = Λ.ε (la + k • e).y ∧ q.g = Λ.ex0 ((k : ℂ)⁻¹ • Λ.A.P0 (la + k • e)) ∧ ∀ q', QkExt (algebraMap _ ℂ) p q' → Out.QkPt.Equiv a.D₀ ℂ q q' := by
  first | exact @GlobalTheory.GtRep.exists_rep_and_shift | exact GlobalTheory.GtRep.exists_rep_and_shift | (intros; apply GlobalTheory.GtRep.exists_rep_and_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNeZeroIff
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ThetaOverField

theorem exists_ne_zero_iff {K : Type} [Field K] (D₀ : Out.DegPre K) (th : D₀.P.L.Sec) :
    (∃ j, th.f j ≠ 0) ↔ ThNZ th := by
  have := D₀.P.isAb.smooth
  have : IsReduced D₀.P.A.left := isReduced_scheme_of_smooth_of_isIntegrallyClosed K D₀.P.A.hom
  constructor
  · rintro ⟨j, hj⟩ y
    by_contra hn
    refine hj ((basicOpen_eq_bot_iff _).1 (eq_bot_iff.2 fun z hz => hn ⟨z, ?_, ?_⟩))
    · exact Subsingleton.elim (α := PrimeSpectrum K) _ _
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hz⟩
  · intro h
    obtain ⟨x, -, hx⟩ := h (IsLocalRing.closedPoint K)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    refine ⟨j, fun e => ?_⟩
    rw [e, Scheme.basicOpen_zero] at hj
    exact hj

theorem nonzero_generates : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] (D₀ : Out.DegPre K) (th : D₀.P.L.Sec), ((∃ j, th.f j ≠ 0) ↔ ThNZ th) ∧ (ThNZ th → ∀ th' : D₀.P.L.Sec, ∃! r : K, ThMul r th th') ∧ ∃ th₀ : D₀.P.L.Sec, ThNZ th₀ := by
  intro hL _ K _ D₀ th
  refine ⟨exists_ne_zero_iff D₀ th, fun h th' => ?_, ?_⟩
  · have refl : LBIso D₀.P.L (D₀.P.L.pull (𝟙 _)) :=
      LBIso.chartPull (chartPullUnpull D₀.P.L _ rfl) (chartPullId _)
        (exists_iso_linComb (F := 𝟙 D₀.P.A.left) D₀.P.isLB (fun _ : PUnit => 𝟙 _) (fun _ => 1) fun _ _ _ => rfl)
    exact GlobalTheory.SectionBaseChange.generates hL.secBaseChange D₀.P (t := 𝟙 _) (φ := 𝟙 _)
      (IsPullback.of_horiz_isIso ⟨by simp⟩) D₀.P.isLB refl th h th'
  · obtain ⟨b, hb, -⟩ := GlobalTheory.KeyOnPol.exists_generator hL.secBaseChange D₀.P
    exact ⟨b, hb⟩

end GlobalTheory.ThetaOverField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowMulEqSumConstantExpansionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_eq_sum_constantExpansion : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (j : ℕ) (σ : Out.H0 W.P.U.LG.L j), 1 ≤ j → ∃ (N n : ℕ) (r : Fin n → ℂ⟦X⟧) (s : Fin n → Out.H0 W.P.U.LG.L j), (∀ i, HasConstExp W (s i)) ∧ ∀ (Z : Type) [CommRing Z] [IsLocalRing Z] (κ : ℂ⟦X⟧ →+* Z) (p : Sp Z ⟶ W.t.G.left) (k : W.P.U.LG.L.ι), p ≫ W.t.G.hom = spMap κ → ⊤ ≤ p ⁻¹ᵁ W.P.U.LG.L.U k → κ PowerSeries.X ^ N * FormalValue.secVal W.P.U.toUnifPre σ p k = ∑ i, κ (r i) * FormalValue.secVal W.P.U.toUnifPre (s i) p k := by
  first | exact @GlobalTheory.ConstExpSpan.exists_pow_mul_eq_sum | exact GlobalTheory.ConstExpSpan.exists_pow_mul_eq_sum | (intros; apply GlobalTheory.ConstExpSpan.exists_pow_mul_eq_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSectionValuesFormalThetaSumStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_values_formalThetaSum : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (j : ℕ) [NeZero j] (α : Λ.A.X), ∀ th ∈ Λ.A.Theta j α, ∃ (m : ℕ) (σ : Out.H0 W.P.U.LG.L j), Ξ.Vals σ (fun v => HahnSeries.single (m : ℤ) (1 : ℂ) * Λ.A.FSum j α th v) := by
  first | exact @GlobalTheory.ConstThetaSections.exists_vals_fsum | exact GlobalTheory.ConstThetaSections.exists_vals_fsum | (intros; apply GlobalTheory.ConstThetaSections.exists_vals_fsum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueThetaOfStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_thetaOf_alt : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (th : a.D₀.P.L.Sec), ThNZ th → (∃! θ : LB.Sec W.t.PP.L, ThetaOf W th θ) ∧ ∀ θ, ThetaOf W th θ → (∀ s : LB.Sec W.t.PP.L, ∃! r : PowerSeries A, ∀ i, s.f i = constFn W.t.G.hom _ r * θ.f i) ∧ (∃ g : W.t.G.left, W.t.G.hom g = IsLocalRing.closedPoint (PowerSeries A) ∧ g ∈ Out.nonzeroLocus θ) ∧ ∀ (r : A) (th' : a.D₀.P.L.Sec) (θ' : LB.Sec W.t.PP.L), ThMul r th th' → (ThetaOf W th' θ' ↔ ∀ i, θ'.f i = constFn W.t.G.hom _ (PowerSeries.C (R := A) r) * θ.f i) := by
  first | exact @GlobalTheory.existsUnique_thetaOf | exact GlobalTheory.existsUnique_thetaOf | (intros; apply GlobalTheory.existsUnique_thetaOf <;> assumption)
end

