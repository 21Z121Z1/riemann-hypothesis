import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0033
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0037
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0079
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0039
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFrameChangeByConstants
section
noncomputable section

namespace GlobalTheory.ArcQ.FrLin

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

section Const

variable {R : Type} [CommRing R] {X Z : Scheme.{0}}

theorem res_const (p : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a := by
  exact congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := U) le_top (homOfLE h).op)

theorem appLE_const (p : X ⟶ Sp R) (f : Z ⟶ X) {U : X.Opens} {V : Z.Opens} (h : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V h).hom (constFn p U a) = constFn (f ≫ p) V a := by
  exact congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE f p ⊤ U V le_top h)

theorem const_spMap {S : Type} [CommRing S] (φ : R →+* S) (q : X ⟶ Sp S) (U : X.Opens) (a : R) :
    constFn (q ≫ spMap φ) U a = constFn q U (φ a) := by
  have N := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at N
  unfold constFn
  rw [N, ← Scheme.Hom.appLE_comp_appLE q (spMap φ) ⊤ ⊤ U le_top le_top, CommRingCat.comp_apply]
  congr 2

def smulSec (p : X ⟶ Sp R) (a : R) {L : LB X} (s : LB.Sec L) : LB.Sec L where
  f j := constFn p _ a * s.f j
  compat i j := by
    rw [map_mul, map_mul, s.compat i j, res_const, res_const]
    ring

theorem isoMaps_smul (p : X ⟶ Sp R) (a : R) {L M : LB X} {w : LB.Iso L M} {s : LB.Sec L} {s' : LB.Sec M}
    (h : IsoMaps w s s') : IsoMaps w (smulSec p a s) (smulSec p a s') := by
  intro i k
  have e := h i k
  simp only [smulSec]
  rw [map_mul, map_mul, e, res_const, res_const]
  exact mul_left_comm _ _ _

end Const

theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap φ := by
  rw [SecCalc.spMap_comp', SecCalc.spMap_comp']
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem comb_transport {R S : Type} [CommRing R] [CommRing S] (io : R →+* S) {x : Sp S ⟶ Xo.X} {G : SAB H (Sp S)}
    {t : SAB H (Sp R)} (m1 : SABMap G Xo.univ.t x) (m2 : SABMap G t (spMap io)) {n : ℕ} (cf : Fin n → R)
    (v : Fin n → (epsR R ⟶ t.G)) (w : epsR R ⟶ t.G) (hw : IsLieComb cf v w) (q : Fin n → (epsR S ⟶ G.G))
    (hq : ∀ i, (q i).left ≫ m2.φ = spMap (dualMap io) ≫ (v i).left)
    (u : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (hu : IsCombAt x (fun i => (q i).left ≫ m1.φ) (fun i => io (cf i)) u) :
    ∃ u' : Sp (DualNumber S) ⟶ G.G.left, u' ≫ m1.φ = u ∧ u' ≫ m2.φ = spMap (dualMap io) ≫ w.left ∧
      u' ≫ G.G.hom = spMap (algebraMap S (DualNumber S)) := by
  have wb : w.left ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) := Over.w w
  have cond : (spMap (dualMap io) ≫ w.left) ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ spMap io := by
    rw [Category.assoc, wb, dual_alg]
  let w' : epsR S ⟶ G.G := Over.homMk (m2.cart.1.lift _ _ cond) (m2.cart.1.lift_snd _ _ cond)
  have hw' : w'.left ≫ m2.φ = spMap (dualMap io) ≫ w.left := m2.cart.1.lift_fst _ _ cond
  have hc : IsLieComb (fun i => io (cf i)) q w' := Chart.comb_baseChange io m2.cart hw hq hw'
  obtain ⟨p, hp, hpp⟩ := (Chart.comb_push m1.cart _ _ _).1 hc
  obtain ⟨p', hp', hpp'⟩ := hu
  obtain rfl : p = p' := funext fun i => Over.OverMorphism.ext ((hp i).trans (hp' i).symm)
  exact ⟨w'.left, hpp.symm.trans hpp', hw', Over.w w'⟩

end GlobalTheory.ArcQ.FrLin

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open GlobalTheory.ArcQ.FrLin

theorem isArcFr_of_frChg_const : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (e e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th th' : a.D₀.P.L.Sec) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A) (r : A), ThNZ th → (∀ τ k, GtComb (g τ k) (e τ) (e' τ k)) → ThMul r th th' → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι : PowerSeries A →+* S) (y y' : FrPt Xo c S), Mono Y.j → IsArcFr W e th ι y → FrChg (fun τ => (g τ).map (ι.comp (PowerSeries.C (R := A)))) (ι (PowerSeries.C (R := A) r)) y y' → IsArcFr W e' th' ι y' := by
  intro hL hL2 E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W e e' th th' g r hth hg hr S _ _ io y y' _ hy hchg
  obtain ⟨x', xo', u', t1', t2', t3', s', t4'⟩ := y'
  obtain ⟨hx, hcomb, hs⟩ := hchg
  dsimp only at hx hcomb hs
  subst hx
  obtain ⟨z, G, m1, m2, φ, zj, zx, φb, φ1, φ2, hu, θ, w1, w2, σ, s1, θ2, hθ, r1, r2, i1, i2, ps, hgx⟩ := hy
  have key : ∀ τ k, ∃ (v : epsR (PowerSeries A) ⟶ W.t.G) (q : epsR S ⟶ G.G), LieImg W (e τ k) v ∧
      q.left ≫ m1.φ = y.u τ k ∧ q.left ≫ m2.φ = spMap (dualMap io) ≫ v.left := fun τ k => by
    obtain ⟨v, p, h1, h2, h3, h4⟩ := hu τ k
    exact ⟨v, Over.homMk p h4, h1, h2, h3⟩
  choose v q hv hq1 hq2 using key
  have hθ' : ThetaOf W th' (smulSec W.t.G.hom (PowerSeries.C (R := A) r) θ) :=
    (((GlobalTheory.existsUnique_thetaOf hL hL2 E H Dw l Xo c O β Y A b a χ W th hth).2 θ hθ).2.2 r th' _ hr).2 fun _ => rfl
  have hs' : ∀ i, s'.f i = scal y.x (io (PowerSeries.C (R := A) r)) i * y.s.f i :=
    ((SecCalc.sec_calc E H Dw l Xo S S S (RingHom.id S) (RingHom.id S) y.x y.x y.x
      (by rw [SecCalc.spMap_id', Category.id_comp]) (by rw [SecCalc.spMap_id', Category.id_comp])).2.1 _ _ _).1 hs
  refine ⟨z, G, m1, m2, φ, zj, zx, φb, φ1, φ2, fun τ k => ?_, _, w1, w2,
    smulSec G.G.hom (io (PowerSeries.C (R := A) r)) σ, smulSec G.G.hom (io (PowerSeries.C (R := A) r)) s1,
    smulSec G.G.hom (io (PowerSeries.C (R := A) r)) θ2, hθ', r1, r2, isoMaps_smul _ _ i1, isoMaps_smul _ _ i2,
    fun j h => ?_, fun gx g1 g2 j h => ?_⟩
  · obtain ⟨w, hw, -⟩ := (GlobalTheory.ConstLie.main hL.globalFns E H Dw l Xo c O β Y A b a χ W (e' τ k)).1
    have hc := (GlobalTheory.ConstLin.lieImg_iff_isLieComb hL.globalFns E H Dw l Xo c O β Y A b a χ W _ (g τ k) (e τ) (e' τ k) (v τ) w (hv τ)
      (hg τ k)).1 hw
    have hy : y.u τ = fun i => (q τ i).left ≫ m1.φ := funext fun i => (hq1 τ i).symm
    obtain ⟨p, p1, p2⟩ := comb_transport io m1 m2 _ (v τ) w hc (q τ) (hq2 τ) (u' τ k) (hy ▸ hcomb τ k)
    exact ⟨w, p, hw, p1, p2⟩
  · show constFn _ _ _ * θ2.f j = (m2.φ.appLE _ _ h).hom (constFn _ _ _ * θ.f _)
    rw [map_mul, ← ps j h, appLE_const, m2.cart.1.w, const_spMap]
  · refine Eq.trans ?_ (congrArg (gx.appLE _ _ h).hom (hs' _)).symm
    refine Eq.trans ?_ (map_mul _ _ _).symm
    refine congrArg₂ (· * ·) ?_ (hgx gx g1 g2 j h)
    exact ((appLE_const _ gx h _).trans (congrArg (fun p => constFn p _ _) g2)).symm

end GlobalTheory.ArcQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcModelWitnessExtension
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcTheta

theorem omegaStd_single_inl {g : ℕ} (u : Fin g ⊕ Fin g → ℤ) (k : Fin g) :
    omegaStd u (Pi.single (.inl k) 1) = -u (.inr k) := by
  simp [omegaStd, Pi.single_apply]

theorem mem_span_single_inl {g : ℕ} (S : Finset (Fin g)) (u : Fin g ⊕ Fin g → ℤ) :
    u ∈ Submodule.span ℤ ((fun k => (Pi.single (Sum.inl k) 1 : Fin g ⊕ Fin g → ℤ)) '' (S : Set (Fin g))) ↔
      (∀ k, u (.inr k) = 0) ∧ ∀ k ∉ S, u (.inl k) = 0 := by
  first
  | exact @_root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff
  | exact _root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff
  | (apply _root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff ..)

theorem exists_adapted {Λ : Type} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (ω : LinearMap.BilinForm ℤ Λ) (hω : ∀ x, ω x x = 0) (hp : Function.Bijective ω) {g : ℕ}
    (hg : Module.finrank ℤ Λ = 2 * g) (K : Λ → Prop)
    (h1 : ∀ t, (∀ v, K v → ω t v = 0) → K t)
    (h2 : ∀ v, (∀ t, (∀ v', K v' → ω t v' = 0) → ω t v = 0) → K v) :
    ∃ (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] Λ) (S : Finset (Fin g)),
      (∀ u v, ω (bas u) (bas v) = -omegaStd u v) ∧ (∀ u, K (bas u) ↔ ∀ k ∈ S, u (.inr k) = 0) ∧
      ∀ u, (∀ v', K v' → ω (bas u) v' = 0) ↔ (∀ k, u (.inr k) = 0) ∧ ∀ k ∉ S, u (.inl k) = 0 := by
  let I : Submodule ℤ Λ :=
    { carrier := {t | ∀ v, K v → ω t v = 0}
      add_mem' := fun ha hb v hv => by simp [ha v hv, hb v hv]
      zero_mem' := fun v _ => by simp
      smul_mem' := fun r x hx v hv => by simp [hx v hv] }
  have halt : ω.IsAlt := hω
  obtain ⟨g', bas, S, hs, hI, hr⟩ := GlobalTheory.exists_symplectic_coordinates_adapted halt hp (I := I)
    (fun k x hk hx v hv => by
      have := hx v hv
      simpa [hk] using this)
    (fun x hx y hy => hx y (h1 y hy)) (ε := -1) (Or.inr rfl)
  obtain rfl : g' = g := by omega
  have hs' : ∀ u v, ω (bas u) (bas v) = -omegaStd u v := fun u v => by rw [hs]; ring
  have horth : ∀ u, bas u ∈ I ↔ (∀ k, u (.inr k) = 0) ∧ ∀ k ∉ S, u (.inl k) = 0 := fun u => by
    rw [← mem_span_single_inl, hI]
    have : (fun k => bas (Pi.single (Sum.inl k) 1)) '' (S : Set (Fin g')) =
        bas.toLinearMap '' ((fun k => (Pi.single (Sum.inl k) 1 : Fin g' ⊕ Fin g' → ℤ)) '' (S : Set (Fin g'))) := by
      rw [Set.image_image]; rfl
    rw [this, ← Submodule.map_span]
    exact Submodule.mem_map_equiv _ |>.trans (by simp)
  refine ⟨bas, S, hs', fun u => ⟨fun hu k hk => ?_, fun hu => h2 _ fun t ht => ?_⟩, horth⟩
  · have hm : bas (Pi.single (Sum.inl k) 1) ∈ I := by
      rw [hI]; exact Submodule.subset_span ⟨k, hk, rfl⟩
    have := hm _ hu
    rw [← halt.neg_eq, hs', omegaStd_single_inl] at this
    simpa using this
  · obtain ⟨t, rfl⟩ := bas.surjective t
    obtain ⟨e1, e2⟩ := (horth t).1 ht
    rw [hs', omegaStd, neg_eq_zero]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ∈ S
    · simp [e1, hu k hk]
    · simp [e1, e2 k hk]

theorem isThetaFrameAt_of_isThetaFrame {g m : ℕ} {S : Scheme.{0}} {G : Over S} [GrpObj G] (L : RigLB G)
    (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ S)) (e : (Fin m → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ G.left))
    (θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ) (h : IsThetaFrame L B y e θ) (b : Fin m → ℂ) (hb : b ∈ B) :
    ∃ fr, IsThetaFrameAt L (y b) (e b) (θ b) fr := by
  obtain ⟨fr, h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun j z => fr j (b, z), fun j => ?_, fun j z => h2 j b z hb, fun j j' z => h3 j j' b z hb,
    fun j => h4 j b hb, h5 b hb⟩
  exact (h1 j).comp ((differentiable_const b).prodMk differentiable_id).differentiableOn fun z hz => ⟨hb, hz⟩

theorem exists_isRigIso {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (L' : RigLB t'.G)
    (hL : L' = t'.PP) : ∃ w : LB.Iso L'.L (t.PP.L.pull m.φ), IsRigIso m.cm L' t.PP w := by
  subst hL
  obtain ⟨w, h1, h2, -⟩ := m.lin
  exact ⟨w, h1, h2⟩

theorem nonempty_thetaDat : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu), IsTypeFn H Dw.p Dw.q ty → ∀ th : a.D₀.P.L.Sec, ThNZ th → Nonempty (ThetaDat Ha th) := by
  intro hL hL2 E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha _ th hth
  obtain ⟨nn, hN, hbe, -, hnn, hker, -⟩ := GlobalTheory.ArcQ.holArc_nilpotent E H Dw l Xo c σ O β Y a χ W g ty Fu Ha
  let w₀ : ℂ := ((Ha.T + 1 : ℝ) : ℂ) * Complex.I
  have hw₀ : Ha.T < w₀.im := by simp [w₀]
  obtain ⟨-, hinj, hdisc, hsp, -⟩ := Ha.period w₀ hw₀
  obtain ⟨hfree, hfin, hrk⟩ := GlobalTheory.free_finite_finrank_of_discrete_span _ hinj hdisc hsp
  obtain ⟨bas, S, hs, hk, horth⟩ := exists_adapted (Fu.Di Ha.i).EF (Fu.Di Ha.i).alt (Fu.Di Ha.i).unimod hrk
    (fun v => Ha.y v = 0) hker (fun v hv => by
      by_contra hne
      have h0 := hv (nn v) fun v' hv' => by
        have := hbe v v'
        rw [hv', map_zero, neg_eq_zero] at this
        exact this
      have h1 := hbe v v
      have h2 := a.be_pos _ hne
      rw [h0] at h1
      omega)
  have hconst : ∀ w k, Ha.Pw w (bas (Pi.single (.inl k) 1)) = Ha.P₀ (bas (Pi.single (.inl k) 1)) := fun w k => by
    rw [Ha.Pw_eq, hN, hnn _ ((hk _).2 fun j _ => by simp), map_zero, smul_zero, add_zero]
  have hR := (GlobalTheory.RiemannRel.riemann_relations E H (Fu.Di Ha.i) g ty bas hs).1
  obtain ⟨h, τ₀, hh, -⟩ := hR _ (Ha.period w₀ hw₀)
  let τ : ℂ → Matrix (Fin g) (Fin g) ℂ := fun w =>
    h * Matrix.of fun i j => Ha.Pw w (bas (Pi.single (.inr j) 1)) i
  have hper : ∀ w k, h.mulVec (Ha.Pw w (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧
      h.mulVec (Ha.Pw w (bas (Pi.single (.inr k) 1))) = (τ w).mulVec (Pi.single k 1) := fun w k => by
    refine ⟨by rw [hconst, ← hconst w₀]; exact (hh k).1, ?_⟩
    rw [← Matrix.mulVec_mulVec, GlobalTheory.RiemannRel.of_cols_mulVec (fun j => Ha.Pw w (bas (Pi.single (.inr j) 1))) k]
  have hpos : ∀ w, Ha.T < w.im → (τ w).IsSymm ∧ ((τ w).map Complex.im).PosDef := fun w hw => by
    obtain ⟨h', τ', -, -, e1, e2, hu⟩ := hR _ (Ha.period w hw)
    rw [(hu h (τ w) (hper w)).2]
    exact ⟨e1, e2⟩
  let B : Set (Fin 1 → ℂ) := {b | Ha.T < (b 0).im}
  have hBo : IsOpen B := isOpen_lt continuous_const (by fun_prop)
  have hBc : IsPreconnected B := by
    refine Convex.isPreconnected (?_ : Convex ℝ B)
    exact (convex_halfSpace_im_gt Ha.T).linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0)
  obtain ⟨c₁, c₂, hc₁, hc₂, hfr⟩ := Fu.theta Ha.i 1 B (fun b => Ha.Pw (b 0)) bas (-1) (fun _ => h) (fun b => τ (b 0))
    hBo hBc ⟨fun b hb => Ha.period _ hb, fun x => by
      simp only [Ha.Pw_eq]
      fun_prop⟩ (fun u v => by rw [hs]; simp) (fun b hb => ⟨(hpos _ hb).2, hper _⟩)
  have hframe : ∀ w, Ha.T < w.im → ∃ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u Ha.i (Ha.Pw w))
      (fun z => (Fu.ex Ha.i (Ha.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr := fun w hw =>
    isThetaFrameAt_of_isThetaFrame _ _ _ _ _ hfr (fun _ => w) hw
  obtain ⟨⟨θ, ⟨s, fam, -, hex, hfam, -⟩, -⟩, -⟩ := GlobalTheory.T.existsUnique_thetaOf_alt hL hL2 E H Dw l Xo c O β Y ℂ (σ.comp β) a χ W th hth
  obtain ⟨w₂, hw₂⟩ := exists_isRigIso W.m W.P.U.LG W.P.bundle
  obtain ⟨w₁, hw₁⟩ := exists_isRigIso Y.m _ rfl
  obtain ⟨w₃, hw₃⟩ := exists_isRigIso Y.m0.toSABMap _ rfl
  have hne : ∃ j, th.f j ≠ 0 := by
    obtain ⟨x, -, hx⟩ := hth (IsLocalRing.closedPoint ℂ)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    refine ⟨j, fun e => ?_⟩
    rw [e, Scheme.basicOpen_zero] at hj
    exact hj
  obtain ⟨fr₀, hfr₀⟩ := hframe w₀ hw₀
  obtain ⟨κ, hκ, hS, hB, -⟩ := Ha.theta th s fam bas S h τ c₁ c₂ w₂ w₁ w₃ hne hex hfam hs hk hper hc₁ hc₂
    hw₂ hw₁ hw₃ ⟨w₀, fr₀, hw₀, hfr₀⟩
  exact ⟨⟨bas, S, h, τ, c₁, c₂, κ, hs, hk, horth, hper, hpos, hc₁, hc₂, hframe, hκ, hS, hB⟩⟩

end GlobalTheory.ArcTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantPointFrameIsFrameWithRigidificationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantPointFrame_isFrame_with_rigidification : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) , (∀ v, IsFrm W.P.U.LG.L (Ξ.x v).left (Ξ.τ v)) ∧ ∀ j, ⊤ ≤ (Ξ.x 0).left ⁻¹ᵁ W.P.U.LG.L.U j → Ξ.τ 0 j = valR (𝟙 (Sp ℂ⟦X⟧)) ((W.P.U.LG.L.pull (eSec W.t.G)).U (fun _ => j)) (W.P.U.LG.rig.s (fun _ => j)).val := by
  first | exact @GlobalTheory.ConstFrame.main | exact GlobalTheory.ConstFrame.main | (intros; apply GlobalTheory.ConstFrame.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsAbelianTripleIsoOfSamePointValuesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianTriple_iso_of_same_point_values : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (s : Sp F ⟶ Sp B) (o₁ o₂ : Obj D l bb s) (Θ₁ : FPts act o₁.t (𝟙 _) φ) (Θ₂ : FPts act o₂.t (𝟙 _) φ), ∃ (m : SABMap o₁.t o₂.t (𝟙 _)) (w : LB.Iso o₁.t.PP.L (o₂.t.PP.L.pull m.φ)), IsRigIso m.cm o₁.t.PP o₂.t.PP w ∧ ∀ v, (Θ₁.x v).left ≫ m.φ = (Θ₂.x v).left ∧ ∀ j j', ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ (LB.div (o₂.t.PP.L.pull m.φ) o₁.t.PP.L).U (fun _ => j, j') → Θ₂.τ v j = valR (Θ₁.x v).left _ (w.s (fun _ => j, j')).val * Θ₁.τ v j' := by
  first | exact @GlobalTheory.FamilyIso.exists_sabMap_of_same_values | exact GlobalTheory.FamilyIso.exists_sabMap_of_same_values | (intros; apply GlobalTheory.FamilyIso.exists_sabMap_of_same_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArcStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ν : Out.GtPt a.D₀ (epsR A)), (∃! v : epsR (PowerSeries A) ⟶ W.t.G, LieImg W ν v) ∧ ∀ v, LieImg W ν v → (GtTanR ν ↔ IsTangent v) := by
  first | exact @GlobalTheory.ConstLie.main | exact GlobalTheory.ConstLie.main | (intros; apply GlobalTheory.ConstLie.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtTanRIffVanishes
section
noncomputable section

namespace GlobalTheory.ConstModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
  Formalism.L2.Pj.QAt
open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)
open scoped CategoryTheory.Obj

section Bundles

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]

def SecThrough (w : LB.Iso L' (L.pull Φ)) (s : LB.Sec L) (s' : LB.Sec L') : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, Φ (r z) ∈ L.U j → r z ∈ L'.U k →
    gs (r ≫ Φ) z _ (s.f j) = (Geo.Tor.gw w r z j k).val * gs r z _ (s'.f k)

theorem SecThrough.mem {w : LB.Iso L' (L.pull Φ)} {s : LB.Sec L} {s' : LB.Sec L'} (h : SecThrough w s s')
    (hL' : L'.IsLB) {x : X'} (hx : Φ x ∈ nonzeroLocus s) : x ∈ nonzeroLocus s' := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hj' : Φ x ∈ L.U j := X.basicOpen_le _ hj
  obtain ⟨k, hk⟩ := exists_chart hL' x
  have u : IsUnit (gs (𝟙 X) (Φ x) _ (s.f j)) := by
    rw [gs_eq (𝟙 X) (Φ x) _ hj']; exact (X.mem_basicOpen _ _ hj').1 hj
  have e := h _ (𝟙 _) x j k hj' hk
  rw [Category.id_comp, gs_stalkMap Φ x _ hj'] at e
  have u' : IsUnit (gs (𝟙 X') x _ (s'.f k)) := isUnit_of_mul_isUnit_right (e ▸ u.map _)
  rw [gs_eq (𝟙 X') x _ hk] at u'
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, (X'.mem_basicOpen _ _ hk).2 u'⟩

end Bundles

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' T'' : Over (Sp R)}

def Vanishes (k : T' ⟶ T) (g : GtPt D T) : Prop :=
  k ≫ g.b = 1 ∧ ∀ χ (Z : Scheme.{0}) (r : Z ⟶ T'.left) (z : Z) J, Good D.P.L z J → val (g.s χ) (r ≫ k.left) z J = 1

theorem Vanishes.comp {k : T' ⟶ T} {g : GtPt D T} (h : Vanishes k g) (k' : T'' ⟶ T') : Vanishes (k' ≫ k) g :=
  ⟨by rw [Category.assoc, h.1, MonObj.comp_one], fun χ Z r z J hJ => by
    rw [Over.comp_left, ← Category.assoc]; exact h.2 χ Z _ z J hJ⟩

def epsZero (R : Type) [CommRing R] : Over.mk (𝟙 (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom)
    ((spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun _ => rfl)).trans (Spec.map_id (CommRingCat.of R))))

end Points

section Through

variable {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R'']
  {f : R →+* R'} {f' : R' →+* R''} {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''}

def Through (p : IsPullDeg f D D') {T : Over (Sp R)} {T' : Over (Sp R')} (h : T'.left ⟶ T.left) (g : GtPt D T)
    (g' : GtPt D' T') : Prop :=
  ∀ y, (∀ k, DegPre.gtφT D' T' g'.b y k ≫ proj p = h ≫ DegPre.gtφT D T g.b (p.xe y) k) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ T'.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (g.s (p.xe y)) (r ≫ h) z J =
        (∏ k, om p.w z J J' (r ≫ DegPre.gtφT D' T' g'.b y k) ^ DegPre.gtε k) * val (g'.s y) r z J'

structure IsComp (p : IsPullDeg f D D') (q : IsPullDeg f' D' D'') (r : IsPullDeg (f'.comp f) D D'') : Prop where
  proj_eq : proj r = proj q ≫ proj p
  xe_eq : ∀ x, r.xe x = p.xe (q.xe x)
  tri : ∀ (Y : Scheme.{0}) (x : Y ⟶ D''.P.A.left) (y : Y) j i k, proj p (proj q (x y)) ∈ D.P.L.U j →
    proj q (x y) ∈ D'.P.L.U i → x y ∈ D''.P.L.U k →
    Geo.Tor.gw r.w x y j k = Geo.Tor.gw p.w (x ≫ proj q) y j i * Geo.Tor.gw q.w x y i k

namespace IsComp

variable {p : IsPullDeg f D D'} {q : IsPullDeg f' D' D''} {r : IsPullDeg (f'.comp f) D D''} (C : IsComp p q r)
include C

theorem om_eq {Z : Scheme.{0}} {z : Z} {J J' J''} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J')
    (hJ'' : Good D''.P.L z J'') (x : Z ⟶ D''.P.A.left) :
    om r.w z J J'' x = om p.w z J J' (x ≫ proj q) * om q.w z J' J'' x := by
  have e : x ≫ proj r = (x ≫ proj q) ≫ proj p := (congrArg (x ≫ ·) C.proj_eq).trans (Category.assoc _ _ _).symm
  exact (congrArg (fun u => Geo.Tor.gw r.w x z (J u) (J'' x)) e).trans
    (C.tri Z x z _ _ _ (hJ ((x ≫ proj q) ≫ proj p)) (hJ' (x ≫ proj q)) (hJ'' x))

theorem isPullGtF {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
    [Algebra (FractionRing R'') F] (hF : Compat (f'.comp f) F) (hF' : Compat f' F) {g : GtPtF D F} {g' : GtPtF D' F}
    {g'' : GtPtF D'' F} (H : IsPullGtF f p F g g') (H' : IsPullGtF f' q F g' g'') :
    IsPullGtF (f'.comp f) r F g g'' := by
  refine isPullGtF_of_val r hF ?_ fun χ y J J'' hJ hJ'' => ?_
  · rw [C.proj_eq, ← Category.assoc]
    exact (congrArg (· ≫ proj p) H'.1).trans H.1
  · obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB (Z := Sp F) y
    have v := pullGt_val p H (q.xe χ) (𝟙 _) hJ hJ'
    have v' := pullGt_val q H' χ (𝟙 _) hJ' hJ''
    obtain ⟨hψ, -⟩ := H'.2 χ
    have a₀ : (cP D'' _ χ * g''.b).left ≫ proj q = 𝟙 _ ≫ (cP D' _ (q.xe χ) * g'.b).left := hψ 0
    have a₁ : (cP D'' (TF (R := R'') F) χ).left ≫ proj q = 𝟙 _ ≫ (cP D' (TF (R := R') F) (q.xe χ)).left := hψ 1
    have a₂ : g''.b.left ≫ proj q = 𝟙 _ ≫ g'.b.left := hψ 2
    have a₃ : (1 : TF (R := R'') F ⟶ D''.P.A).left ≫ proj q = 𝟙 _ ≫ (1 : TF (R := R') F ⟶ D'.P.A).left := hψ 3
    simp only [Category.id_comp] at v'
    rw [C.xe_eq, C.om_eq hJ hJ' hJ'', C.om_eq hJ hJ' hJ'', C.om_eq hJ hJ' hJ'', C.om_eq hJ hJ' hJ'', a₀, a₁, a₂, a₃]
    have alg : ∀ (U : Type) [CommGroup U] (a b c d a' b' c' d' v : U), a⁻¹ * b * c * d⁻¹ * (a'⁻¹ * b' * c' * d'⁻¹ * v) =
        (a * a')⁻¹ * (b * b') * (c * c') * (d * d')⁻¹ * v := fun U _ a b c d a' b' c' d' v => by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    exact (v.trans (congrArg₂ (· * ·) rfl v')).trans (alg _ _ _ _ _ _ _ _ _ _)

end IsComp

end Through

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)]

def powerSeriesCDVR (K : Type) [Field K] [CharZero K] : Formalism.L2.Pj.CDVR :=
  haveI : CharZero (PowerSeries K) := algebraRat.charZero _
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries K)) (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  ⟨PowerSeries K⟩

def powerSeriesConst (K : Type) [Field K] [CharZero K] : K →+* (powerSeriesCDVR K).V := PowerSeries.C (R := K)

end GlobalTheory.ConstModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LevelPointsOfArcEqPeriodDivLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPoints_of_arc_eq_period_div_level : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (Φ : GenPts Λ.A W.t gen) (yF : Sp ℂ⸨X⸩ ⟶ Xo.XF c) (k : ℕ) (p₀ : Out.QkPt a.D₀ (FractionRing ℂ) k) (ξ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (la : Λ.A.La) (p : Over.mk gen ⟶ W.t.G), Ξ.IsGen Φ → yF ≫ Y.j = gen ≫ χ → ((k = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ ξ = Y.oF.etaA v) ∨ (k = l.M ∧ ∃ v ∈ idealPart D l, HEq p₀ (a.eta v) ∧ ξ = Y.oF.eta v)) → Λ.Rep k p₀ la → p.left ≫ W.m.φ = yF ≫ ξ.left ≫ Y.m.φ → Φ.LevelPt k p la := by
  first | exact @GlobalTheory.levelPt_of_rep | exact GlobalTheory.levelPt_of_rep | (intros; apply GlobalTheory.levelPt_of_rep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieCombStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (m : ℕ) (cf : Fin m → A) (e : Fin m → Out.GtPt a.D₀ (epsR A)) (ν : Out.GtPt a.D₀ (epsR A)) (v : Fin m → (epsR (PowerSeries A) ⟶ W.t.G)) (w : epsR (PowerSeries A) ⟶ W.t.G), (∀ i, LieImg W (e i) (v i)) → GtComb cf e ν → (LieImg W ν w ↔ IsLieComb (fun i => PowerSeries.C (R := A) (cf i)) v w) := by
  first | exact @GlobalTheory.ConstLin.lieImg_iff_isLieComb | exact GlobalTheory.ConstLin.lieImg_iff_isLieComb | (intros; apply GlobalTheory.ConstLin.lieImg_iff_isLieComb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentConstantDirectionSpecialisesDerivStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_constant_direction_specialises_deriv : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), AnFin A → Φ.Rational → ∀ (z₀ : A.V) (ν : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback o.t.G.hom y), Φ.IsTan z₀ ν → ∃ T' ≥ Ψ.T, ∀ (w : ℂ) (hw : Ψ.T < w.im), T' < w.im → ∃ νt : Sp (DualNumber (Γ.R w)) ⟶ o.t.G.left, νt ≫ o.t.G.hom = spMap (algebraMap (Γ.R w) (DualNumber (Γ.R w))) ≫ spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT ∧ (∀ ρ : DualNumber (Γ.R w) →+* DualNumber ℂ⸨X⸩, (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (r : ℂ⸨X⸩)) → ρ DualNumber.eps = DualNumber.eps → spMap ρ ≫ νt = ν ≫ pullback.fst _ _) ∧ ∀ ρ : DualNumber (Γ.R w) →+* DualNumber ℂ, (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (Γ.ev w r)) → ρ DualNumber.eps = DualNumber.eps → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ ≫ νt = (Ψ.pi w 0).left ∧ ∀ (W : o.t.G.left.Opens) (f : Γ(o.t.G.left, W)), ⊤ ≤ (Ψ.pi w 0).left ⁻¹ᵁ W → TrivSqZeroExt.snd (valR (spMap ρ ≫ νt) W f) = fderiv ℂ (fun v => valAt' (Ψ.pi w v).left W f) 0 z₀ := by
  first | exact @GlobalTheory.SpecTangent.spec_tangent | exact GlobalTheory.SpecTangent.spec_tangent | (intros; apply GlobalTheory.SpecTangent.spec_tangent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TripleIsoRespectsLevelRatioPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_iso_respects_level_ratio_points : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (s : Sp F ⟶ Sp B) (o₁ o₂ : Obj D l bb s) (Θ₁ : FPts act o₁.t (𝟙 _) φ) (Θ₂ : FPts act o₂.t (𝟙 _) φ) (m : SABMap o₁.t o₂.t (𝟙 _)) (w : LB.Iso o₁.t.PP.L (o₂.t.PP.L.pull m.φ)) (k : ℕ) (ψ : I k → V → F) (p₁ : Over.mk (𝟙 (Sp F)) ⟶ o₁.t.G) (p₂ : Over.mk (𝟙 (Sp F)) ⟶ o₂.t.G), 1 ≤ k → w.IsGen → (∀ v, (Θ₁.x v).left ≫ m.φ = (Θ₂.x v).left ∧ ∀ j j', ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ (LB.div (o₂.t.PP.L.pull m.φ) o₁.t.PP.L).U (fun _ => j, j') → Θ₂.τ v j = valR (Θ₁.x v).left _ (w.s (fun _ => j, j')).val * Θ₁.τ v j') → Θ₁.Lev k p₁ ψ → Θ₂.Lev k p₂ ψ → p₁.left ≫ m.φ = p₂.left := by
  first | exact @GlobalTheory.LevelRespect.level_pt_eq | exact GlobalTheory.LevelRespect.level_pt_eq | (intros; apply GlobalTheory.LevelRespect.level_pt_eq <;> assumption)
end

