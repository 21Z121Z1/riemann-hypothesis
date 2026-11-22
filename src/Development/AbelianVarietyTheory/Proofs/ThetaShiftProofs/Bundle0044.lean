import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsIntegralElemOfIsAlgebraicInt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0043
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumArcLieBasis
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ArcQ.DatumBasis

open MonoidalCategory CartesianMonoidalCategory MonObj Matrix

section Coord

open GlobalTheory.Serre

variable {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (a : OAct O G)
  {g : ℕ} {B : Fin g → (epsR R ⟶ G)} (hB : IsLieBasis B)
include hB

theorem comb_iff_symm (z : Fin g → R) (w : epsR R ⟶ G) :
    IsLieComb z B w ↔ w = ((Lie.basis a hB).equivFun.symm z).hom := by
  have e : B = fun i => (Lie.basis a hB i).hom := funext fun i => (Lie.hom_basis hB i).symm
  rw [Module.Basis.equivFun_symm_apply, ← Lie.isLieComb_iff, ← e]

include a in

theorem exists_comb (z : Fin g → R) : ∃ w, IsTangent w ∧ IsLieComb z B w :=
  ⟨_, Lie.isTangent _, (comb_iff_symm a hB z _).2 rfl⟩

include a in

theorem comb_coord {m : ℕ} {U : Fin m → Fin g → R} {u : Fin m → (epsR R ⟶ G)} (hU : ∀ k, IsLieComb (U k) B (u k))
    {z : Fin g → R} {w : epsR R ⟶ G} (hz : IsLieComb z B w) (cf : Fin m → R) :
    IsLieComb cf u w ↔ z = ∑ k, cf k • U k := by
  obtain rfl : u = fun k => ((Lie.basis a hB).equivFun.symm (U k)).hom :=
    funext fun k => (comb_iff_symm a hB _ _).1 (hU k)
  obtain rfl := (comb_iff_symm a hB _ _).1 hz
  rw [Lie.isLieComb_iff, ← (Lie.basis a hB).equivFun.symm.injective.eq_iff, map_sum]
  simp only [map_smul]
  exact ⟨fun h => Lie.ext h, fun h => congrArg Lie.hom h⟩

theorem eig_coord {x : O} {M : Matrix (Fin g) (Fin g) R} (hM : ∀ i, IsLieComb (M i) B (B i ≫ a.act x))
    {z : Fin g → R} {w : epsR R ⟶ G} (hz : IsLieComb z B w) (s : R) :
    (w ≫ a.act x).left = spMap (epsScaleR s) ≫ w.left ↔ z ᵥ* M = s • z := by
  obtain rfl := (comb_iff_symm a hB _ _).1 hz
  have h1 : ∀ i, x • Lie.basis a hB i = (Lie.basis a hB).equivFun.symm (M i) := fun i => Lie.ext (by
    rw [Lie.hom_act_smul, Lie.hom_basis]; exact (comb_iff_symm a hB _ _).1 (hM i))
  have h2 : x • (Lie.basis a hB).equivFun.symm z = (Lie.basis a hB).equivFun.symm (z ᵥ* M) := by
    rw [Matrix.vecMul_eq_sum, map_sum, Module.Basis.equivFun_symm_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm x, h1, map_smul]
  rw [← Lie.hom_act_smul, ← Lie.hom_smul_left, h2, ← map_smul,
    ← (Lie.basis a hB).equivFun.symm.injective.eq_iff]
  exact ⟨fun h => Lie.ext (Over.OverMorphism.ext h), fun h => by rw [h]⟩

theorem eigBasis_coord {M : O → Matrix (Fin g) (Fin g) R} (hM : ∀ x i, IsLieComb (M x i) B (B i ≫ a.act x))
    {m : ℕ} {U : Fin m → Fin g → R} {u : Fin m → (epsR R ⟶ G)} (hU : ∀ k, IsLieComb (U k) B (u k)) (ρ : O → R) :
    (∀ w : epsR R ⟶ G, IsTangent w → (∀ x, (w ≫ a.act x).left = spMap (epsScaleR (ρ x)) ≫ w.left) →
      ∃! cf : Fin m → R, IsLieComb cf u w) ↔
    ∀ z : Fin g → R, (∀ x, z ᵥ* M x = ρ x • z) → ∃! cf : Fin m → R, z = ∑ k, cf k • U k := by
  constructor
  · intro h z hz
    obtain ⟨w, hw, hc⟩ := exists_comb a hB z
    exact (existsUnique_congr (comb_coord a hB hU hc)).1
      (h w hw fun x => (eig_coord a hB (hM x) hc _).2 (hz x))
  · intro h w hw he
    obtain ⟨z, hc, -⟩ := hB.2 w hw
    exact (existsUnique_congr (comb_coord a hB hU hc)).2
      (h z fun x => (eig_coord a hB (hM x) hc _).1 (he x))

end Coord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem dual_over {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap φ := by
  rw [← spMap_comp, ← spMap_comp]
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

section Descent

variable {R S : Type} [CommRing R] [CommRing S] {io : R →+* S} {t : SAB H (Sp R)} {t' : SAB H (Sp S)}
  (m : SABMap t' t (spMap io))

theorem exists_bc (v : epsR R ⟶ t.G) : ∃ q : epsR S ⟶ t'.G, q.left ≫ m.φ = spMap (dualMap io) ≫ v.left := by
  have hv : v.left ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) := Over.w v
  have cond : (spMap (dualMap io) ≫ v.left) ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ spMap io := by
    rw [Category.assoc, hv, dual_over]
  exact ⟨Over.homMk (m.cart.1.lift _ _ cond) (m.cart.1.lift_snd _ _ _), m.cart.1.lift_fst _ _ _⟩

theorem tangent_of_bc [IsDomain R] (hio : Function.Injective io) {v : epsR R ⟶ t.G} {q : epsR S ⟶ t'.G}
    (h : q.left ≫ m.φ = spMap (dualMap io) ≫ v.left) (hq : IsTangent q) : IsTangent v := by
  have hv : v.left ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) := Over.w v
  have := t.semi.separated
  have : IsDominant (spMap io) := ⟨by
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical io).2 ?_
    rw [(RingHom.injective_iff_ker_eq_bot io).1 hio]; exact bot_le⟩
  refine ext_of_isDominant_of_isSeparated t.G.hom ?_ (spMap io) ?_
  · have a : η[t.G].left ≫ t.G.hom = 𝟙 _ := Over.w η[t.G]
    rw [Category.assoc, hv, a, ← spMap_comp]
    have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext r; simp
    rw [this]
    exact Spec.map_id _
  · have e := m.cm.e_comm
    rw [m.base] at e
    have sq : spMap io ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom =
        spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap io) := by
      rw [← spMap_comp, ← spMap_comp]
      congr 1
      exact RingHom.ext fun a => by simp [dualMap]
    rw [← Category.assoc, sq, Category.assoc, ← h, ← Category.assoc]
    exact (congrArg (· ≫ m.φ) hq).trans e

end Descent

theorem eigBasis_descent {K S : Type} [Field K] [CommRing S] [Nontrivial S] {io : PowerSeries K →+* S}
    {t : SAB H (Sp (PowerSeries K))} {t' : SAB H (Sp S)} (m : SABMap t' t (spMap io))
    {g : ℕ} {B : Fin g → (epsR (PowerSeries K) ⟶ t.G)} (hB : IsLieBasis B) {M : 𝓞 E → Matrix (Fin g) (Fin g) K}
    (hM : ∀ x i, IsLieComb (fun k => PowerSeries.C (R := K) (M x i k)) B (B i ≫ t.act.act x))
    {n : ℕ} {U : Fin n → Fin g → K} {v : Fin n → (epsR (PowerSeries K) ⟶ t.G)}
    (hU : ∀ k, IsLieComb (fun i => PowerSeries.C (R := K) (U k i)) B (v k)) {q : Fin n → (epsR S ⟶ t'.G)}
    (hq : ∀ k, (q k).left ≫ m.φ = spMap (dualMap io) ≫ (v k).left) (ρ : 𝓞 E → K)
    (he : ∀ k x, (q k ≫ t'.act.act x).left = spMap (epsScaleR (io (PowerSeries.C (R := K) (ρ x)))) ≫ (q k).left)
    (hb : ∀ w : epsR S ⟶ t'.G, IsTangent w →
      (∀ x, (w ≫ t'.act.act x).left = spMap (epsScaleR (io (PowerSeries.C (R := K) (ρ x)))) ≫ w.left) →
      ∃! cf : Fin n → S, IsLieComb cf q w) :
    (∀ k x, (v k ≫ t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := K) (ρ x))) ≫ (v k).left) ∧
    ∀ w : epsR (PowerSeries K) ⟶ t.G, IsTangent w →
      (∀ x, (w ≫ t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := K) (ρ x))) ≫ w.left) →
      ∃! cf : Fin n → PowerSeries K, IsLieComb cf v w := by
  let _ : Algebra K S := (io.comp (PowerSeries.C (R := K))).toAlgebra
  have := t.semi.smooth
  choose B' hB' using fun i => exists_bc m (B i)
  have hBS : IsLieBasis B' := Chart.isLieBasis_baseChange io m.cart hB hB'
  have hMS : ∀ x i, IsLieComb (((M x).map (algebraMap K S)) i) B' (B' i ≫ t'.act.act x) := fun x i =>
    Chart.comb_baseChange io m.cart (hM x i) hB' (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, hB', Category.assoc]; rfl)
  have hUS : ∀ k, IsLieComb (fun j => algebraMap K S (U k j)) B' (q k) := fun k =>
    Chart.comb_baseChange io m.cart (hU k) hB' (hq k)
  have hMR : ∀ x i, IsLieComb (((M x).map (algebraMap K (PowerSeries K))) i) B (B i ≫ t.act.act x) := hM
  have hUR : ∀ k, IsLieComb (fun j => algebraMap K (PowerSeries K) (U k j)) B (v k) := hU
  have key : ∀ (T : Type) [CommRing T] (f : K →+* T) (k : Fin n) (x : 𝓞 E) (j : Fin g),
      f ((U k ᵥ* M x) j) = ((fun j => f (U k j)) ᵥ* (M x).map f) j := fun T _ f k x j =>
    RingHom.map_vecMul f (M x) (U k) j
  have hK : ∀ k x, U k ᵥ* M x = ρ x • U k := fun k x => funext fun j => (algebraMap K S).injective (by
    rw [key, (eig_coord t'.act hBS (hMS x) (hUS k) (algebraMap K S (ρ x))).1 (he k x)]
    simp)
  refine ⟨fun k x => (eig_coord t.act hB (hMR x) (hUR k) (algebraMap K _ (ρ x))).2 (funext fun j => ?_),
    (eigBasis_coord t.act hB hMR hUR fun x => algebraMap K _ (ρ x)).2 ?_⟩
  · rw [← key, hK]; simp
  · exact (GlobalTheory.commonEigenvectors_flat_baseChange K (𝓞 E) g n M ρ).1 S U hK
      ((eigBasis_coord t'.act hBS hMS hUS fun x => algebraMap K S (ρ x)).1 hb) (PowerSeries K)

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section Push

variable {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {t' : SAB H (Sp S)} (m : SABMap t' Xo.univ.t x)

theorem tan_iff (w : epsR S ⟶ t'.G) : IsTanAt x (w.left ≫ m.φ) ↔ IsTangent w := by
  have hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w w
  exact ⟨fun h => (Chart.tan_push m.cart w).2 h.2,
    fun h => ⟨by rw [Category.assoc, m.cart.1.w, ← Category.assoc, hw], (Chart.tan_push m.cart w).1 h⟩⟩

theorem eig_iff (w : epsR S ⟶ t'.G) (a : 𝓞 E) (s : S) :
    (w.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left = spMap (epsMul s) ≫ w.left ≫ m.φ ↔
      (w ≫ t'.act.act a).left = spMap (epsScaleR s) ≫ w.left := by
  have hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w w
  have e : (w.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left = (w ≫ t'.act.act a).left ≫ m.φ := by
    rw [Over.comp_left, Category.assoc, Category.assoc, m.act]
  have sc : spMap (epsScaleR s) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap S (DualNumber S)) := by
    rw [← spMap_comp]
    congr 1
    ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e]
  constructor
  · intro h
    apply m.cart.1.hom_ext
    · rw [Category.assoc]; exact h
    · rw [Over.w, Category.assoc, hw, sc]; rfl
  · intro h
    rw [h, Category.assoc]; rfl

theorem comb_iff {n : ℕ} (v : Fin n → (epsR S ⟶ t'.G)) (cf : Fin n → S) (w : epsR S ⟶ t'.G) :
    IsCombAt x (fun i => (v i).left ≫ m.φ) cf (w.left ≫ m.φ) ↔ IsLieComb cf v w :=
  (Chart.comb_push m.cart cf v w).symm

end Push

end GlobalTheory.ArcQ.DatumBasis

open GlobalTheory.ArcQ.DatumBasis in

theorem GlobalTheory.ArcQ.arcDatum_arcLieBasis : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁), (∀ τ k, GtTanR (d.e τ k)) → ArcLieBasis d.W d.e := by
  intro hL hL2 E _ _ _ H Dw l Xo c K₁ _ _ d htan
  obtain ⟨ζ, -, -, -, hN, -⟩ := GlobalTheory.T.exists_normalForm_arcDatum_framedPoint_rootOfUnity hL hL2 E H Dw l Xo c K₁ d
  obtain ⟨y, hy, -⟩ := hN htan
  obtain ⟨-, G, m1, m2, -, -, -, -, -, -, h, -⟩ := hy
  choose v p hv hp1 hp2 hp3 using h
  let q : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR (ArcS Dw K₁) ⟶ G.G) := fun τ k => Over.homMk (p τ k) (hp3 τ k)
  have hq1 : ∀ τ k, (q τ k).left ≫ m1.φ = y.u τ k := hp1
  have hq2 : ∀ τ k, (q τ k).left ≫ m2.φ = spMap (dualMap (arcι Dw K₁)) ≫ (v τ k).left := hp2
  have hι : Function.Injective (arcι Dw K₁) := (GlobalTheory.ArcConst.algebraMap_injective Dw K₁).comp
    ((MvPolynomial.C_injective _ _).comp HahnSeries.ofPowerSeries_injective)
  have := GlobalTheory.ArcConst.isDomain Dw K₁
  have tq : ∀ τ k, IsTangent (q τ k) := fun τ k => (tan_iff m1 _).1 (hq1 τ k ▸ y.tan τ k)
  have tv : ∀ τ k, IsTangent (v τ k) := fun τ k => tangent_of_bc m2 hι (hq2 τ k) (tq τ k)
  obtain ⟨g, e₀, B, M, h₀, hB, hc, hM⟩ := GlobalTheory.ConstLie.exists_const_basis hL.globalFns E H Dw l Xo c _ _ d.Y K₁ _ _ d.χ d.W
  have hU : ∀ τ k, ∃ U : Fin g → K₁, IsLieComb (fun i => PowerSeries.C (R := K₁) (U i)) B (v τ k) := fun τ k => by
    obtain ⟨U, hU, -⟩ := hc (d.e τ k)
      (((GlobalTheory.ConstLie.main hL.globalFns E H Dw l Xo c _ _ d.Y K₁ _ _ d.χ d.W (d.e τ k)).2 _ (hv τ k)).2 (tv τ k))
    exact ⟨U, (GlobalTheory.ConstLin.lieImg_iff_isLieComb hL.globalFns E H Dw l Xo c _ _ d.Y K₁ _ _ d.χ d.W g U e₀ (d.e τ k) B (v τ k)
      (fun i => (h₀ i).2) hU).1 (hv τ k)⟩
  choose U hU using hU
  have eig : ∀ (τ : E →+* ℂ) (w : epsR (ArcS Dw K₁) ⟶ G.G), IsEigAt c τ (w.left ≫ m1.φ) ↔
      ∀ x : 𝓞 E, (w ≫ G.act.act x).left = spMap (epsScaleR (arcι Dw K₁
        (PowerSeries.C (R := K₁) (algebraMap c.F K₁ (embK c τ x))))) ≫ w.left :=
    fun τ w => forall_congr' fun x => by rw [← arcS_pin]; exact eig_iff m1 w x _
  refine ⟨v, hv, fun τ => ?_⟩
  have hu : y.u τ = fun k => (q τ k).left ≫ m1.φ := funext fun k => (hq1 τ k).symm
  obtain ⟨a₁, a₂⟩ := eigBasis_descent m2 hB hM (hU τ) (hq2 τ) (fun x => algebraMap c.F K₁ (embK c τ x))
    (fun k => (eig τ _).1 (hq1 τ k ▸ y.eig τ k)) fun w hw he =>
      (existsUnique_congr fun cf => by rw [hu]; exact comb_iff m1 (q τ) cf w).1
        (y.basis τ _ ((tan_iff m1 w).2 hw) ((eig τ w).2 he))
  exact ⟨fun k => ⟨tv τ k, a₁ k⟩, a₂⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointValueIsHomogeneousLettersStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcFramedPoint_value_isHomogeneous_letters : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (K₁ : Type) [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)] (d : ArcDatum Xo c K₁) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), F ∈ sec Xo c a n → ∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁), algebraMap _ (ArcS Dw K₁) P = evR Xo c F d.yF ∧ P.IsHomogeneous (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ))) := by
  first | exact @GlobalTheory.ArcQ.evR_arc_isHomogeneous | exact GlobalTheory.ArcQ.evR_arc_isHomogeneous | (intros; apply GlobalTheory.ArcQ.evR_arc_isHomogeneous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterAnalyticVectorsIndependentBlockTypeStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_letter_analyticVectors_independent_blockType : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) [Algebra c.F ℂ⸨X⸩] (y : FrPt Xo c ℂ⸨X⸩) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), GoodEmb c σ → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → Mono Y.j → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ i, AnVec Ha (e τ i) (z τ i)) → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) := by
  first | exact @GlobalTheory.ArcType.main | exact GlobalTheory.ArcType.main | (intros; apply GlobalTheory.ArcType.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcSectionValueAtSpecialisedPointsTheta
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section
namespace GlobalTheory.ArcSectionValue

theorem valR_res_const_res {A K : Type} [CommRing A] [CommRing K] {Z : Scheme.{0}} (p : Z ⟶ Sp K) (f : K →+* A)
    (q : Sp A ⟶ Z) (hq : q ≫ p = spMap f) {U U' V : Z.Opens} (h : V ≤ U) (h' : V ≤ U') (hV : ⊤ ≤ q ⁻¹ᵁ V)
    (a : Γ(Z, U)) (r : K) (b : Γ(Z, U')) :
    valR q V (resG Z h a * constFn p V r * resG Z h' b) = valR q U a * f r * valR q U' b := by
  rw [← HolHom.valR_res q h a hV, ← HolHom.valR_res q h' b hV, ← valR_const p f q hq V hV]
  simp only [HolHom.valR_eq _ V hV, map_mul]

theorem germ_identity {Γ : Germs} {w : ℂ} {Z Z' : Scheme.{0}} (x : Sp (Γ.R w) ⟶ Z) (φ : Z ⟶ Z') {xF : Sp ℂ⸨X⸩ ⟶ Z}
    (hx : spMap (Γ.R w).val.toRingHom ≫ x = xF) {U₀ U₁ : Z.Opens} {U : Z'.Opens} (h₀ : ⊤ ≤ x ⁻¹ᵁ U₀)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ U₁) (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U) {a₀ : Γ(Z, U₀)} {a₁ : Γ(Z, U₁)} {s : Γ(Z', U)} {ρ : ℂ⸨X⸩}
    (e : valR xF U₀ a₀ * valR (xF ≫ φ) U s = valR xF U₁ a₁ * ρ) :
    ((valR x U₀ a₀ : Γ.R w) : ℂ⸨X⸩) * (valR (x ≫ φ) U s : Γ.R w) = (valR x U₁ a₁ : Γ.R w) * ρ := by
  subst hx
  rwa [Category.assoc, HolHom.valR_spMap _ _ _ h₀, HolHom.valR_spMap _ _ _ h₁, HolHom.valR_spMap _ _ _ h] at e

theorem ev_identity {Γ : Germs} {w : ℂ} {Z Z' : Scheme.{0}} (x : Sp (Γ.R w) ⟶ Z) (φ : Z ⟶ Z')
    {U₀ U₁ : Z.Opens} {U : Z'.Opens} (h₀ : ⊤ ≤ x ⁻¹ᵁ U₀)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ U₁) (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U) {a₀ : Γ(Z, U₀)} {a₁ : Γ(Z, U₁)} {s : Γ(Z', U)} {T T' : ℝ}
    (hw : T < w.im) (hw' : T' < w.im) (ρ : Conv.halfRing T) (F : Conv.halfRing T') {t : Γ.R w}
    (e : ((valR x U₀ a₀ : Γ.R w) : ℂ⸨X⸩) * (valR (x ≫ φ) U s : Γ.R w) = (valR x U₁ a₁ : Γ.R w) * (ρ * F * t)) :
    valAt' (spMap (Γ.ev w).toRingHom ≫ x) U₀ a₀ * valAt' ((spMap (Γ.ev w).toRingHom ≫ x) ≫ φ) U s =
      valAt' (spMap (Γ.ev w).toRingHom ≫ x) U₁ a₁ * (Conv.ev T w hw ρ * Conv.ev T' w hw' F * Γ.ev w t) := by
  have e' : valR x U₀ a₀ * valR (x ≫ φ) U s = valR x U₁ a₁ *
      (Subalgebra.inclusion (Γ.le T w hw) ρ * Subalgebra.inclusion (Γ.le T' w hw') F * t) := Subtype.ext e
  have e'' := congrArg (Γ.ev w) e'
  rw [map_mul, map_mul, map_mul, map_mul, Γ.ev_eq, Γ.ev_eq] at e''
  rw [HolHom.valAt'_eq_valR, HolHom.valAt'_eq_valR, HolHom.valAt'_eq_valR, Category.assoc,
    HolHom.valR_spMap _ _ _ h₀, HolHom.valR_spMap _ _ _ h₁, HolHom.valR_spMap _ _ _ h]
  exact e''

theorem mem_convLaurent_of_germ {Γ : Germs} {w : ℂ} {x₀ y x₁ t : Γ.R w} {ρ F : ℂ⸨X⸩}
    (e : (x₀ : ℂ⸨X⸩) * y = x₁ * (ρ * F * t)) (h₁ : IsUnit x₁) (ht : IsUnit t) (hF : F ≠ 0)
    (hF' : F ∈ Conv.convLaurent) : ρ ∈ Conv.convLaurent := by
  have u₁ : (x₁ : ℂ⸨X⸩) ≠ 0 := (h₁.map (Γ.R w).val).ne_zero
  have u₀ : (t : ℂ⸨X⸩) ≠ 0 := (ht.map (Γ.R w).val).ne_zero
  have : ρ = x₀ * y / (x₁ * F * t) := by
    rw [e]
    field_simp
  rw [this]
  exact div_mem (mul_mem (germ_mem_convLaurent Γ w _) (germ_mem_convLaurent Γ w _))
    (mul_mem (mul_mem (germ_mem_convLaurent Γ w _) hF') (germ_mem_convLaurent Γ w _))

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable {Y : Model Xo c β} [Algebra (FractionRing ℂ) ℂ] {bF : c.F →+* ℂ} {a : ArcIn D l β ℂ (bF.comp β)}
  {χ : Sp ℂ⟦X⟧ ⟶ Y.X}
  {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : GtAn a}

theorem isProper_gen (C : Chain W Λ) : IsProper (pullback.snd W.t.G.hom gen) := by
  haveI := Y.oF.proper
  have h1 : IsPullback (pullback.fst W.t.G.hom gen ≫ W.m.φ) (pullback.snd W.t.G.hom gen) Y.t.G.hom (gen ≫ χ) :=
    (IsPullback.of_hasPullback W.t.G.hom gen).paste_horiz W.m.cart.1
  have h2 : IsPullback (pullback.fst Y.oF.t.G.hom C.yF ≫ Y.m.φ) (pullback.snd Y.oF.t.G.hom C.yF) Y.t.G.hom
      (C.yF ≫ Y.j) := (IsPullback.of_hasPullback Y.oF.t.G.hom C.yF).paste_horiz Y.m.cart.1
  rw [C.yF_j] at h2
  rw [← h1.isoIsPullback_hom_snd _ _ h2]
  infer_instance

theorem valR_section_model (hL : Out.Laws) (hL2 : Out.Laws2) (C : Chain W Λ) {σ : Out.H0 W.P.U.LG.L 1}
    {f : Λ.A.V → ℂ⸨X⸩} (hf : C.Ξ.Vals σ f) {w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)}
    (hw₂ : IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂) {U : Y.X.Opens} (hU : ⊤ ≤ χ ⁻¹ᵁ U)
    {s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)} {r : PowerSeries ℂ} (hp : PullHyp W σ w₂ U s r)
    (v : Λ.A.V) (j : Y.t.PP.L.ι) (hj : ⊤ ≤ (C.ΦY.x v).left ⁻¹ᵁ Y.t.PP.L.U j) :
    valR (C.ΦY.x v).left _ (s j) = (r : ℂ⸨X⸩) * f v * C.ΦY.τ v j := by
  obtain ⟨k₁, hk₁⟩ := exists_chart_local (A := ℂ⟦X⟧) (C.Ξ.x v).left W.P.U.LG.isLB
  obtain ⟨w', k₂, hw', hk, hUk, hval⟩ := exists_rigIso_of_eq (A := ℂ⸨X⸩) W.m.cm W.P.bundle Y.t.PP w₂ hw₂ k₁
  obtain ⟨hx, hτ⟩ := C.isGen v
  obtain ⟨hxY, hrel⟩ := C.rel₂.2 v
  have hk₁' : ⊤ ≤ (C.ΦW.x v).left ⁻¹ᵁ W.P.U.LG.L.U k₁ := hx ▸ FormalValue.top_le_comp hk₁ _
  have hj' : ⊤ ≤ ((C.ΦW.x v).left ≫ W.m.φ) ⁻¹ᵁ Y.t.PP.L.U j := hxY ▸ hj
  have hd₁ := (le_div_iff (C.ΦW.x v).left W.m.φ Y.t.PP.L W.P.U.LG.L j k₁).2 ⟨hj', hk₁'⟩
  have hd₂ := (le_div_iff (C.ΦW.x v).left W.m.φ Y.t.PP.L W.t.PP.L j k₂).2 ⟨hj', hUk ▸ hk₁'⟩
  have hw := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres hL hL2 E H _ _ Y.t W.t χ W.m).2 w' C.w₂ hw' C.rig₂ _ gen (C.ΦW.x v) (isProper_gen C) j k₂ hd₂
  have hover : (C.ΦW.x v).left ≫ W.t.G.hom = gen := Over.w (C.ΦW.x v)
  have h₁ : ⊤ ≤ (C.ΦW.x v).left ⁻¹ᵁ (W.m.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)) := by
    have : ⊤ ≤ ((C.ΦW.x v).left ≫ W.m.φ ≫ Y.t.G.hom) ⁻¹ᵁ U := by
      rw [W.m.cart.1.w, reassoc_of% hover]
      exact FormalValue.top_le_comp hU _
    exact fun z hz => ⟨this hz, hj' hz⟩
  have h₃ : ⊤ ≤ (C.Ξ.x v).left ⁻¹ᵁ LB.wchart W.P.U.LG.L (fun _ : Fin 1 => 𝟙 W.t.G.left) (fun _ => k₁) :=
    fun z hz => Set.mem_iInter.2 fun _ => hk₁ hz
  have h₃' : ⊤ ≤ (C.ΦW.x v).left ⁻¹ᵁ LB.wchart W.P.U.LG.L (fun _ : Fin 1 => 𝟙 W.t.G.left) (fun _ => k₁) :=
    hx ▸ FormalValue.top_le_comp h₃ _
  let V : W.t.G.left.Opens := W.m.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j) ⊓
    ((LB.div (Y.t.PP.L.pull W.m.φ) W.P.U.LG.L).U (fun _ => j, k₁) ⊓
      LB.wchart W.P.U.LG.L (fun _ : Fin 1 => 𝟙 W.t.G.left) (fun _ => k₁))
  have hV : ⊤ ≤ (C.ΦW.x v).left ⁻¹ᵁ V := fun z hz => ⟨h₁ hz, hd₁ hz, h₃' hz⟩
  have key := ((HolHom.valR_appLE _ _ _ _ _ _ hV).symm.trans (congrArg (valR (C.ΦW.x v).left V)
    (hp j k₁ V inf_le_left (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)))).trans
    (valR_res_const_res _ _ _ hover _ _ hV _ _ _)
  have hσ : valR (C.ΦW.x v).left _ (σ.f (fun _ => k₁)) = f v * C.ΦW.τ v k₂ := by
    rw [hτ k₁ k₂ hk hk₁, ← pow_one (algebraMap ℂ⟦X⟧ ℂ⸨X⸩ _), ← hf v k₁ hk₁, hx]
    exact HolHom.valR_spMap _ _ _ h₃ _
  rw [← hxY, hrel j k₂ hd₂, ← hw, ← hval]
  refine key.trans ?_
  refine (congrArg (_ * ·) hσ).trans ?_
  change _ * (r : ℂ⸨X⸩) * _ = _
  ring

theorem valR_section_generic (hL : Out.Laws) (hL2 : Out.Laws2) (C : Chain W Λ) {σ : Out.H0 W.P.U.LG.L 1}
    {f : Λ.A.V → ℂ⸨X⸩} (hf : C.Ξ.Vals σ f) {w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)}
    {w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)}
    {w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)}
    (hw₂ : IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂) (hw₁ : IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁)
    (hw₀ : IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀) {U : Y.X.Opens} (hU : ⊤ ≤ χ ⁻¹ᵁ U)
    {s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)} {r : PowerSeries ℂ} (hp : PullHyp W σ w₂ U s r)
    (v : Λ.A.V) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι)
    (h₁ : ⊤ ≤ (C.ΦF.x v).left ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k))
    (h₀ : ⊤ ≤ (C.ΦF.x v).left ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) :
    valR (C.ΦF.x v).left _ (w₀.s (fun _ => j₀, k)).val * valR ((C.ΦF.x v).left ≫ Y.m.φ) _ (s j) =
      valR (C.ΦF.x v).left _ (w₁.s (fun _ => j, k)).val * ((r : ℂ⸨X⸩) * f v * C.Φ.τ v j₀) := by
  haveI := Y.oF.proper
  obtain ⟨hx₁, hr₁⟩ := C.rel₁.2 v
  have e₁ := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres hL hL2 E H _ _ Y.t Y.oF.t _ Y.m).2 w₁ C.w₁ hw₁ C.rig₁ _ C.yF (C.ΦF.x v) inferInstance j k h₁
  have e₀ := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres hL hL2 E H _ _ Xo.univ.t Y.oF.t _ Y.m0.toSABMap).2 w₀ C.w₀ hw₀ C.rig₀ _ C.yF (C.ΦF.x v)
    inferInstance j₀ k h₀
  have hj := ((le_div_iff _ _ _ _ _ _).1 h₁).1
  have e₂ := valR_section_model hL hL2 C hf hw₂ hU hp v j (hx₁ ▸ hj)
  have e₃ := hr₁ j k h₁
  have e₄ := (C.rel₀.2 v).2 j₀ k h₀
  have aux : ∀ {x₀ x₀' x₁ x₁' y ρ t t₀ t₁ : ℂ⸨X⸩}, x₁ = x₁' → x₀ = x₀' → y = ρ * t₁ → t₁ = x₁' * t → t₀ = x₀' * t →
      x₀ * y = x₁ * (ρ * t₀) := by
    rintro _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl
    ring
  exact aux e₁ e₀ ((congrArg (valR · _ (s j)) hx₁).trans e₂) e₃ e₄

variable (hL : Out.Laws) (hL2 : Out.Laws2) (C : Chain W Λ) {σ : Out.H0 W.P.U.LG.L 1}
  {f : Λ.A.V → ℂ⸨X⸩} (hf : C.Ξ.Vals σ f) {w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)}
  {w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)}
  {w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)}
  (hw₂ : IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂) (hw₁ : IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁)
  (hw₀ : IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀) {U : Y.X.Opens} (hU : ⊤ ≤ χ ⁻¹ᵁ U)
  {s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)} {r : PowerSeries ℂ} (hp : PullHyp W σ w₂ U s r)
  {Γ : Germs} (Ψ : SpecPts C.Φ Γ) {w : ℂ} (hw : Ψ.T < w.im) (v : Λ.A.V) (xg : Sp (Γ.R w) ⟶ Y.oF.t.G.left)
  (e₀ : xg ≫ Y.m0.toSABMap.φ = (Ψ.xt w hw v).left) (eg : spMap (Γ.R w).val.toRingHom ≫ xg = (C.ΦF.x v).left)
  (hxU : ⊤ ≤ (xg ≫ Y.oF.t.G.hom) ⁻¹ᵁ (Y.j ⁻¹ᵁ U))

omit [StarRing (𝓞 E)] in
include hxU in

theorem le_section_dom {j : Y.t.PP.L.ι} (hj : ⊤ ≤ (xg ≫ Y.m.φ) ⁻¹ᵁ Y.t.PP.L.U j) :
    ⊤ ≤ (xg ≫ Y.m.φ) ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j) := by
  have : ⊤ ≤ (xg ≫ Y.m.φ ≫ Y.t.G.hom) ⁻¹ᵁ U := by
    rw [Y.m.cart.1.w]
    exact hxU
  exact fun z hz => ⟨this hz, hj hz⟩

include hL hL2 hf hw₂ hw₁ hw₀ hU hp e₀ eg hxU

theorem valR_section_germ (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι)
    (h₁ : ⊤ ≤ xg ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k))
    (h₀ : ⊤ ≤ xg ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) :
    ((valR xg _ (w₀.s (fun _ => j₀, k)).val : Γ.R w) : ℂ⸨X⸩) * (valR (xg ≫ Y.m.φ) _ (s j) : Γ.R w) =
      (valR xg _ (w₁.s (fun _ => j, k)).val : Γ.R w) * ((r : ℂ⸨X⸩) * f v * Ψ.τt w v j₀) := by
  have hs := le_section_dom xg hxU ((le_div_iff _ _ _ _ _ _).1 h₁).1
  have hj₀ := ((le_div_iff _ _ _ _ _ _).1 h₀).1
  rw [e₀] at hj₀
  have h₁' := FormalValue.top_le_comp h₁ (spMap (Γ.R w).val.toRingHom)
  have h₀' := FormalValue.top_le_comp h₀ (spMap (Γ.R w).val.toRingHom)
  rw [eg] at h₁' h₀'
  rw [Ψ.τt_gen w hw v j₀ hj₀]
  exact germ_identity xg Y.m.φ eg h₀ h₁ hs (valR_section_generic hL hL2 C hf hw₂ hw₁ hw₀ hU hp v j k j₀ h₁' h₀')

theorem factor_mem_convLaurent (hv : f v ≠ 0) (hv' : f v ∈ Conv.convLaurent) : (r : ℂ⸨X⸩) ∈ Conv.convLaurent := by
  have := isLocalRing_germ Γ w
  obtain ⟨j, hj⟩ := exists_chart_local (xg ≫ Y.m.φ) Y.t.PP.isLB
  obtain ⟨k, hk⟩ := exists_chart_local xg Y.oF.t.PP.isLB
  obtain ⟨j₀, hj₀⟩ := exists_chart_local (xg ≫ Y.m0.toSABMap.φ) Xo.univ.t.PP.isLB
  have h₁ := (le_div_iff _ _ _ _ _ _).2 ⟨hj, hk⟩
  have h₀ := (le_div_iff _ _ _ _ _ _).2 ⟨hj₀, hk⟩
  have e := valR_section_germ hL hL2 C hf hw₂ hw₁ hw₀ hU hp Ψ hw v xg e₀ eg hxU j k j₀ h₁ h₀
  rw [e₀] at hj₀
  exact mem_convLaurent_of_germ e (FormalValue.isUnit_valR xg _ h₁ _) ((Ψ.τt_frm w hw v).1 j₀ hj₀) hv hv'

theorem valAt_section {T₀ T₂ : ℝ} (hw0 : T₀ < w.im) (hw2 : T₂ < w.im) (hF : f v ∈ Conv.halfRing T₀)
    (hr : (r : ℂ⸨X⸩) ∈ Conv.halfRing T₂) {S : ℂ} (hS : Conv.ev T₀ w hw0 ⟨_, hF⟩ = S) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι)
    (x : Sp ℂ ⟶ Y.oF.t.G.left) (hx : x = spMap (Γ.ev w).toRingHom ≫ xg)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k))
    (h₀ : ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) :
    valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (s j) =
      valAt' x _ (w₁.s (fun _ => j, k)).val *
        (Conv.ev T₂ w hw2 ⟨_, hr⟩ * S * Ψ.fr w j₀ v) := by
  subst hx hS
  have h₁' := le_of_ev Γ w xg h₁
  have h₀' := le_of_ev Γ w xg h₀
  exact ev_identity xg Y.m.φ h₀' h₁' (le_section_dom xg hxU ((le_div_iff _ _ _ _ _ _).1 h₁').1) hw2 hw0 ⟨_, hr⟩ ⟨_, hF⟩
    (valR_section_germ hL hL2 C hf hw₂ hw₁ hw₀ hU hp Ψ hw v xg e₀ eg hxU j k j₀ h₁' h₀')

end Generic

theorem section_value : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x) (θ : (Fin Λ.A.gB → ℂ) → ℂ) (w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)) (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)) (U : Y.X.Opens) (s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)) (r : PowerSeries ℂ), AnFin Λ.A → ThetaHyp W th σ fam → θ ∈ Λ.A.Theta 1 0 → θ ≠ 0 → Λ.u.IsFn th θ → IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂ → IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ → IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ → ⊤ ≤ χ ⁻¹ᵁ U → PullHyp W σ w₂ U s r → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∃ rw : ℂ, SumsAt r w rw ∧ ∀ (v : Λ.A.V) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Ψ.pi w v).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (s j) = valAt' x _ (w₁.s (fun _ => j, k)).val * (rw * Λ.A.Sum 1 0 θ w v * Ψ.fr w j₀ v) := by
  intro hL hL2 E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C Γ Ψ th σ fam θ w₂ w₁ w₀ U s r _ hth hθ hθ0 hfn hw₂ hw₁ hw₀
    hU hp
  have hf := GlobalTheory.T.constantTermWeightZero_section_levelOne_formalSum hL hL2 E H D l Xo c O β Y _ a χ W Λ C.Ξ th σ fam θ hth hθ hfn
  refine Λ.A.exists_isConvLine.elim fun T₀ hT₀ => ?_
  have hF : ∀ v, Λ.A.FSum 1 0 θ v ∈ Conv.halfRing T₀ := fun v _ hw => (AnArc.hasSum_coeff_FSum hT₀ hθ hw v).summable
  have hUF : ⊤ ≤ C.yF ⁻¹ᵁ (Y.j ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, C.yF_j]
    exact FormalValue.top_le_comp hU _
  refine (exists_germ_lift Y bF C.yF_over C.ΦF (fun v => (C.rel₀.2 v).1) Ψ _ hUF).elim fun T₁ hlift => ?_
  have hr : (r : ℂ⸨X⸩) ∈ Conv.convLaurent :=
    (exists_fsum_ne_zero Λ.A hθ0).elim fun v hv =>
      (hlift (((T₁ + 1 : ℝ) : ℂ) * Complex.I) (by simp)).elim fun hw hl => (hl v).elim fun xg h =>
        factor_mem_convLaurent hL hL2 C hf hw₂ hw₁ hw₀ hU hp Ψ hw v xg h.1 h.2.1 h.2.2.1 hv
          (Conv.halfRing_le_convLaurent T₀ (hF v))
  refine (Conv.mem_convLaurent_iff_halfRing.1 hr).elim fun T₂ hT₂ => ⟨max T₀ (max T₁ T₂), fun w hw' => ?_⟩
  have hw0 := (max_lt_iff.1 hw').1
  have hw1 := (max_lt_iff.1 (max_lt_iff.1 hw').2).1
  have hw2 := (max_lt_iff.1 (max_lt_iff.1 hw').2).2
  refine ⟨Conv.ev T₂ w hw2 ⟨_, hT₂⟩, Conv.sumsAt_ev hw2 hT₂, fun v x j k j₀ hx₁ hx₂ h₁ h₀ => ?_⟩
  exact (hlift w hw1).elim fun hw hl => (hl v).elim fun xg h =>
    valAt_section hL hL2 C hf hw₂ hw₁ hw₀ hU hp Ψ hw v xg h.1 h.2.1 h.2.2.1 hw0 hw2 (hF v) hT₂
      (Conv.ev_eq_of_hasSum hw0 ⟨_, hF v⟩ (AnArc.hasSum_coeff_FSum hT₀ hθ hw0 v)) j k j₀ x (h.2.2.2 x hx₁ hx₂) h₁ h₀

end GlobalTheory.ArcSectionValue
end
end

