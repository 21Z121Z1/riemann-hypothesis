import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0006
import Formalism.LocalToGlobal.ProjectiveLattices.GenSpecV
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.IntegralExtensionOfRegR1
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra NumberField IsDedekindDomain Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def RegularityR1 (X : PJ D B P j) (E : PtExt X) : Prop :=
  ∀ w (F : B.Cusp j w), (∀ la (y : X.Pt la), 0 ≤ X.vAt la y (X.inc w F)) →
    ∀ la (y' : E.Pt' la), 0 ≤ E.vAt' la y' (X.inc w F)

def RegularityR2 (X : PJ D B P j) (E : PtExt X)
    (NoZero : ∀ {wL : WeightFamilies.Wt D j} {n : ℕ}, (Fin n → B.Cusp j wL) → Prop) : Prop :=
  (∀ (wL wE : WeightFamilies.Wt D j) (n : ℕ) (gens : Fin n → B.Cusp j wL) (et : B.Cusp j wE)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (c : ℝ), 0 ≤ c → NoZero gens →
    (∀ la (y : X.Pt la), 0 ≤ X.vAt la y (X.inc wE et) ∧ (X.vAt la y (X.inc wE et) ≠ ⊤ →
      (⨅ k, X.vAt la y (X.inc wL (gens k))) ≤
        (((nus la : ℝ) + c * (X.vAt la y (X.inc wE et)).toReal : ℝ) : EReal))) →
    ∀ la (y' : E.Pt' la), 0 ≤ E.vAt' la y' (X.inc wE et) ∧ (E.vAt' la y' (X.inc wE et) ≠ ⊤ →
      (⨅ k, E.vAt' la y' (X.inc wL (gens k))) ≤
        (((nus la : ℝ) + c * (E.vAt' la y' (X.inc wE et)).toReal : ℝ) : EReal))) ∧
  (∀ (wL : WeightFamilies.Wt D j) (n : ℕ) (gens : Fin n → B.Cusp j wL) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    NoZero gens →
    (∀ la (y : X.Pt la), (⨅ k, X.vAt la y (X.inc wL (gens k))) ≤ ((nus la : ℝ) : EReal)) →
    ∀ la (y' : E.Pt' la), (⨅ k, E.vAt' la y' (X.inc wL (gens k))) ≤ ((nus la : ℝ) : EReal))

theorem iInf_span_eq {X : PJ D B P j} {wL : WeightFamilies.Wt D j} {n : ℕ} (g : Fin n → B.Cusp j wL)
    (la : HeightOneSpectrum (𝓞 B.KO)) (v : X.Forms → EReal) (hv0 : v 0 = ⊤)
    (hadd : ∀ F G, min (v F) (v G) ≤ v (F + G))
    (hsmul : ∀ (a : B.KO) F, a ≠ 0 → v (a • F) = (((vAdd la a : ℤ) : ℝ) : EReal) + v F)
    (hint : ∀ a : 𝓞 B.KO, (a : B.KO) ≠ 0 → 0 ≤ vAdd la (a : B.KO)) :
    (⨅ F ∈ Submodule.span (𝓞 B.KO) (Set.range g), v (X.inc wL F)) = ⨅ k, v (X.inc wL (g k)) := by
  apply le_antisymm
  · exact le_iInf fun k => iInf₂_le (g k) (Submodule.subset_span (Set.mem_range_self k))
  · refine le_iInf₂ fun F hF => ?_
    induction hF using Submodule.span_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; exact iInf_le _ k
    | zero => simp [hv0]
    | add x y _ _ hx hy =>
      rw [map_add]; exact le_trans (le_min hx hy) (hadd _ _)
    | smul a x _ hx =>
      by_cases ha : (a : B.KO) = 0
      · have : a = 0 := by exact_mod_cast ha
        subst this; simp [hv0]
      · have hsm : X.inc wL (a • x) = (a : B.KO) • X.inc wL x := by
          rw [← map_smul]; congr 1; exact (algebraMap_smul B.KO a x).symm
        rw [hsm, hsmul _ _ ha]
        have h0 : (0 : EReal) ≤ (((vAdd la (a : B.KO) : ℤ) : ℝ) : EReal) := by
          exact_mod_cast hint a ha
        calc (⨅ k, v (X.inc wL (g k))) = 0 + ⨅ k, v (X.inc wL (g k)) := (zero_add _).symm
          _ ≤ _ := add_le_add h0 hx

def RegTrivK (X : PJ D B P j) (Q : Type) (ord : Q → X.Forms → EReal) : Prop :=
  (∀ w (F : B.Cusp j w), (∀ la (y : X.Pt la), 0 ≤ X.vAt la y (X.inc w F)) →
    ∀ q, 0 ≤ ord q (X.inc w F)) ∧
  (∀ (wL wE : WeightFamilies.Wt D j) (M : Submodule (𝓞 B.KO) (B.Cusp j wL)) (et : B.Cusp j wE)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (c : ℝ), 0 ≤ c →
    (∀ la (y : X.Pt la), 0 ≤ X.vAt la y (X.inc wE et) ∧ (X.vAt la y (X.inc wE et) ≠ ⊤ →
      (⨅ F ∈ M, X.vAt la y (X.inc wL F)) ≤
        (((nus la : ℝ) + c * (X.vAt la y (X.inc wE et)).toReal : ℝ) : EReal))) →
    ∀ q, 0 ≤ ord q (X.inc wE et) ∧ (ord q (X.inc wE et) ≠ ⊤ →
      (⨅ F ∈ M, ord q (X.inc wL F)) ≤ ((c * (ord q (X.inc wE et)).toReal : ℝ) : EReal)))

def gd2Xplus {ka wL wF : WeightFamilies.Wt D j} {X : PJ D B P j} (G : GlobalFamilyData X ka wL wF) (E : PtExt X)
    (hM : IntAtExt X E) : GlobalFamilyData (xplus X E hM) ka wL wF :=
  ⟨G.N, G.w, G.del, G.th', G.rz, G.alz, G.th0, G.zc, G.rq, G.th, G.iet, G.et, G.mx⟩

theorem combBound_xplus {ka wL wF : WeightFamilies.Wt D j} (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E)
    (NoZero : ∀ {wL : WeightFamilies.Wt D j} {n : ℕ}, (Fin n → B.Cusp j wL) → Prop)
    (G : GlobalFamilyData X ka wL wF) (S : Scal B) (c : ℝ) (hc : 0 ≤ c) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hspan : Submodule.span (𝓞 B.KO) (Set.range G.w) = X.WWc S.sW wL) (hNZ : NoZero G.w)
    (hint : ∀ (la : HeightOneSpectrum (𝓞 B.KO)) (a : 𝓞 B.KO), (a : B.KO) ≠ 0 → 0 ≤ vAdd la (a : B.KO))
    (hX : CombBound G S c nus) (hR2 : RegularityR2 X E NoZero) :
    CombBound (gd2Xplus G E hM) S c nus := by
  have dX : ∀ la (y : X.Pt la), X.depth S.sW wL la y = ⨅ k, X.vAt la y (X.inc wL (G.w k)) := by
    intro la y
    unfold PJ.depth
    rw [← hspan]
    exact iInf_span_eq G.w la (X.vAt la y) (X.vAt_zero la y) (X.vAt_add la y) (X.vAt_smul la y) (hint la)
  have dE : ∀ la (y : E.Pt' la), (⨅ F ∈ X.WWc S.sW wL, E.vAt' la y (X.inc wL F)) =
      ⨅ k, E.vAt' la y (X.inc wL (G.w k)) := by
    intro la y
    rw [← hspan]
    exact iInf_span_eq G.w la (E.vAt' la y) (E.vAt'_zero la y) (E.vAt'_add la y) (E.vAt'_smul la y) (hint la)
  intro la y
  cases y with
  | inl y0 => exact hX la y0
  | inr y1 =>
    refine ⟨fun hj => ?_, fun hj => ?_⟩
    · have hc' : 0 ≤ c / (2 * (G.iet : ℝ)) := by positivity
      have := hR2.1 wL _ G.N G.w G.et nus _ hc' hNZ
        (fun la' y => by have h := (hX la' y).1 hj; rw [dX] at h; exact h) la y1
      show 0 ≤ E.vAt' la y1 (X.inc _ G.et) ∧ (E.vAt' la y1 (X.inc _ G.et) ≠ ⊤ →
        (⨅ F ∈ X.WWc S.sW wL, E.vAt' la y1 (X.inc wL F)) ≤ _)
      rw [dE]; exact this
    · have := hR2.2 wL G.N G.w nus hNZ (fun la' y => by have h := (hX la' y).2 hj; rw [dX] at h; exact h) la y1
      show (⨅ F ∈ X.WWc S.sW wL, E.vAt' la y1 (X.inc wL F)) ≤ _
      rw [dE]; exact this

section l2NormAlt

variable (N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ)
    (h0 : ∀ j ka σ F, 0 ≤ N j ka σ F) (h1 : ∀ j ka σ F, N j ka σ F = 0 ↔ F = 0)
    (h2 : ∀ j ka σ (a : B.KO) F, N j ka σ (a • F) = ‖σ a‖ * N j ka σ F)
    (h3 : ∀ j ka σ F G, N j ka σ (F + G) ≤ N j ka σ F + N j ka σ G)
    (h4 : ∀ j ka σ F, N j ka σ F ≤ B.supN j ka σ F)

def gd2XplusN {ka wL wF : WeightFamilies.Wt D j} {X : PJ D B P j} (G : GlobalFamilyData X ka wL wF) (E : PtExt X)
    (hM : IntAtExt X E) : GlobalFamilyData (xplusN N h0 h1 h2 h3 h4 X E hM) ka wL wF :=
  ⟨G.N, G.w, G.del, G.th', G.rz, G.alz, G.th0, G.zc, G.rq, G.th, G.iet, G.et, G.mx⟩

end l2NormAlt

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.LocFrLoc
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart)

private theorem free_range_idem_lemma {V : Type} [CommRing V] [IsLocalRing V] {n : ℕ}
    (g : Module.End V (Fin n → V)) (hg : IsIdempotentElem g) : Module.Free V (LinearMap.range g) := by
  haveI : Module.Projective V (LinearMap.range g) :=
    Module.Projective.of_split (LinearMap.range g).subtype g.rangeRestrict
      (LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext (by
        obtain ⟨y, rfl⟩ := hx
        exact LinearMap.congr_fun hg y))
  exact Module.free_of_flat_of_isLocalRing

theorem finrank_range_idem {V k : Type} [CommRing V] [IsLocalRing V] [Field k] [CharZero k] (f : V →+* k) {n : ℕ}
    (e : Module.End V (Fin n → V)) (e' : Module.End k (Fin n → k)) (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (h : ∀ c, e' (f ∘ c) = f ∘ e c) : Module.finrank V (LinearMap.range e) = Module.finrank k (LinearMap.range e') := by
  classical

  have hker : LinearMap.ker e = LinearMap.range (1 - e) := by
    ext x
    constructor
    · intro hx
      refine ⟨x, ?_⟩
      rw [LinearMap.mem_ker] at hx
      simp [hx]
    · rintro ⟨y, rfl⟩
      have h2 := LinearMap.congr_fun he y
      simp only [Module.End.mul_apply] at h2
      simp [h2]
  haveI := free_range_idem_lemma e he
  haveI : Module.Free V (LinearMap.ker e) := by
    rw [hker]; exact free_range_idem_lemma (1 - e) he.one_sub
  haveI : Module.Finite V (LinearMap.ker e) := by
    rw [hker]; infer_instance
  have hP : LinearMap.IsProj (LinearMap.range e) e :=
    ⟨fun x => LinearMap.mem_range_self e x, fun x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact LinearMap.congr_fun he y⟩
  have hP' : LinearMap.IsProj (LinearMap.range e') e' :=
    ⟨fun x => LinearMap.mem_range_self e' x, fun x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact LinearMap.congr_fun he' y⟩

  have hs : ∀ i : Fin n, (f ∘ Pi.single i (1 : V)) = Pi.single i (1 : k) := by
    intro i
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  have htr : f (LinearMap.trace V _ e) = LinearMap.trace k _ e' := by
    rw [LinearMap.trace_eq_matrix_trace V (Pi.basisFun V (Fin n)),
      LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin n))]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := congrFun (h (Pi.single i 1)) i
    rw [hs i] at this
    exact this.symm
  have h1 := hP.trace
  have h2 := hP'.trace
  apply Nat.cast_injective (R := k)
  rw [← h2, ← htr, h1, map_natCast]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {L : Type} [CommRing L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}

theorem gsvVec_tmap (hx : IsUnivChart _ n xc) (a : 𝓞 E) (cc : Fin n → L) :
    gsvVec x xc (tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) cc) =
      gsvVec x xc cc ≫ (Xo.univ.t.act.act a).left := by
  unfold gsvVec
  rw [ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx, Over.comp_left, Category.assoc, Category.assoc]
  congr 1
  all_goals first
    | rfl
    | (simp; done)
    | (simp [Over.pullback]; done)
    | (simp [Over.pullback, pullback.map]; done)
    | (erw [pullback.lift_fst]; done)
    | (erw [pullback.lift_fst]; rfl)

theorem gsv_bc [IsLocalRing L] {L' : Type} [CommRing L'] [Algebra L L'] (hx : IsUnivChart _ n xc) :
    ∃ (xc' : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L') (JetR L' (Fin n) m) ⟶
        (Over.pullback (spMap (algebraMap L L') ≫ x)).obj Xo.univ.t.G) (hx' : IsUnivChart _ n xc'),
      (∀ cc : Fin n → L, gsvVec (spMap (algebraMap L L') ≫ x) xc' (algebraMap L L' ∘ cc) =
        spMap (dualMap (algebraMap L L')) ≫ gsvVec x xc cc) ∧
      ∀ (a : 𝓞 E) (cc : Fin n → L),
        tmap hx' ((Over.pullback (spMap (algebraMap L L') ≫ x)).map (Xo.univ.t.act.act a)) (algebraMap L L' ∘ cc) =
          algebraMap L L' ∘ tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) cc := by
  obtain ⟨x₁, hx₁, hcomp⟩ := ReciprocityTheory.ChartRestriction.G.Chart.tanBC_alg (R := L) (R' := L') _ n xc hx
  have h₁ := IsGrpPullback.comp
    (isGrpPullback_pullback ((Over.pullback x).obj Xo.univ.t.G) (ReciprocityTheory.ChartRestriction.G.Chart.fB L L'))
    (isGrpPullback_pullback Xo.univ.t.G x)
  obtain ⟨e, he, hφ⟩ := grpPullback_iso h₁
    (isGrpPullback_pullback Xo.univ.t.G (ReciprocityTheory.ChartRestriction.G.Chart.fB L L' ≫ x))
  have hv : ∀ cc : Fin n → L, gsvVec (spMap (algebraMap L L') ≫ x) (fun m => x₁ m ≫ e.hom) (algebraMap L L' ∘ cc) =
      spMap (dualMap (algebraMap L L')) ≫ gsvVec x xc cc := by
    intro cc
    have key : (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap L L' ∘ cc)).left =
        (tvec (x := x₁) (algebraMap L L' ∘ cc)).left ≫ e.hom.left := by
      show (_ ≫ x₁ 1 ≫ e.hom).left = (_ ≫ x₁ 1).left ≫ e.hom.left
      rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc]
    show (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap L L' ∘ cc)).left ≫ pullback.fst _ _ = _
    rw [key, Category.assoc, hφ, ← Category.assoc, hcomp cc, Category.assoc]
    rfl
  have hx' := gfp_chart_iso e hx₁
  refine ⟨fun m => x₁ m ≫ e.hom, hx', hv, fun a cc => gsv_inj hx' ?_⟩
  rw [gsvVec_tmap hx', hv, hv, gsvVec_tmap hx, Category.assoc]

def rhoT (hx : IsUnivChart _ n xc) : 𝓞 E →+* Module.End L (Fin n → L) :=
  have add : ∀ a b, tmap hx ((Over.pullback x).map (Xo.univ.t.act.act (a + b))) =
      tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) + tmap hx ((Over.pullback x).map (Xo.univ.t.act.act b)) :=
    fun a b => LinearMap.ext fun cc => ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx (by
      rw [LinearMap.add_apply, ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx,
        ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx, Xo.univ.t.act.add, Functor.map_mul,
        MonObj.comp_mul])
  { toFun := fun a => tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a))
    map_one' := LinearMap.ext fun cc => gsv_inj hx (by rw [gsvVec_tmap, Xo.univ.t.act.one]; exact Category.comp_id _)
    map_mul' := fun a b => LinearMap.ext fun cc => gsv_inj hx (by
      rw [Module.End.mul_apply, gsvVec_tmap, gsvVec_tmap, gsvVec_tmap, mul_comm a b, Xo.univ.t.act.mul, Category.assoc]; rfl)
    map_zero' := by
      have := add 0 0
      rw [add_zero] at this
      exact left_eq_add.1 this
    map_add' := add }

theorem exists_eig_basis [IsLocalRing L] [Algebra c.F L] (hx0 : x ≫ Xo.s = sOf c L) (hx : IsUnivChart _ n xc) (τ : E →+* ℂ) :
    Nonempty (Module.Basis (Fin (Dw.mult τ)) L
      (eigLat hx (fun a => (Over.pullback x).map (Xo.univ.t.act.act a)) fun a => algebraMap c.F L (embK c τ a))) := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  have key : ∀ {R : Type} [CommRing R] [Algebra c.F R] {x : Sp R ⟶ Xo.X}
      {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (JetR R (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}
      (hx : IsUnivChart _ n xc), IsIdempotentElem (proj (rhoT hx) (embK c) α τ) ∧ LinearMap.range (proj (rhoT hx) (embK c) α τ) =
        eigLat hx (fun a => (Over.pullback x).map (Xo.univ.t.act.act a)) fun a => algebraMap c.F R (embK c τ a) :=
    fun {R} _ _ {x xc} hx => by
      have e₁ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rhoT hx) (embK c τ) (proj (rhoT hx) (embK c) α τ m) := fun m =>
        eig_of_alpha _ _ α hN τ (proj_eig_alpha _ _ α hinj f hf hfs τ m)
      have e₂ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rhoT hx) (embK c τ) m → proj (rhoT hx) (embK c) α τ m = m := fun m hm => by
        have := proj_sum_eig (rhoT hx) (embK c) α hinj (Pi.single τ m) (fun τ' => by
          by_cases h : τ' = τ
          · subst h; rwa [Pi.single_eq_same]
          · rw [Pi.single_eq_of_ne h]; intro a; simp) τ
        rwa [Finset.sum_pi_single', if_pos (Finset.mem_univ _), Pi.single_eq_same] at this
      refine ⟨LinearMap.ext fun m => e₂ _ (e₁ m), Submodule.ext fun m => ?_⟩
      rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
      exact ⟨fun ⟨m', h⟩ => h ▸ e₁ m', fun h => ⟨m, e₂ m h⟩⟩
  let k := IsLocalRing.ResidueField L
  letI : Algebra c.F k := ((algebraMap L k).comp (algebraMap c.F L)).toAlgebra
  have : CharZero k := charZero_of_injective_algebraMap (algebraMap c.F k).injective
  obtain ⟨xc', hx', -, htm⟩ := gsv_bc (L' := k) hx
  have hx0' : (spMap (algebraMap L k) ≫ x) ≫ Xo.s = sOf c k := by
    rw [Category.assoc, hx0]
    exact (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp _ _).symm
  have pw : ∀ (j : ℕ) cc, (rhoT hx' α ^ j) (algebraMap L k ∘ cc) = algebraMap L k ∘ (rhoT hx α ^ j) cc := fun j => by
    induction j with
    | zero => exact fun _ => rfl
    | succ j ih => intro cc; rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]; exact htm α _
  have pr : ∀ (Q : Polynomial c.F) cc, Polynomial.aeval (rhoT hx' α) (Q.map (algebraMap c.F k)) (algebraMap L k ∘ cc) =
      algebraMap L k ∘ Polynomial.aeval (rhoT hx α) (Q.map (algebraMap c.F L)) cc := fun Q cc => by
    induction Q using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.map_add, Polynomial.map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq]
      funext j; simp
    | monomial j a =>
      rw [Polynomial.map_monomial, Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        Module.End.mul_apply, Module.End.mul_apply, pw, Module.algebraMap_end_apply, Module.algebraMap_end_apply]
      funext i
      exact (map_mul (algebraMap L k) _ _).symm
  have r := finrank_range_idem (algebraMap L k) _ _ (key hx).1 (key hx').1 (pr _)
  have := Formalism.L2.Pj.LocFrM.range_free _ (key hx).1
  rw [(key hx').2] at r
  rw [← (key hx).2]
  exact ⟨Module.finBasisOfFinrankEq L _ (r.trans (gfp_finrank hx0' hx' τ))⟩

theorem exists_frPt_local (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) [IsLocalRing L] [Algebra c.F L] (x : Sp L ⟶ Xo.X)
    (hx0 : x ≫ Xo.s = sOf c L) : ∃ y : FrPt Xo c L, y.x = x := by
  have := Xo.univ.t.semi.smooth
  have : Smooth ((Over.pullback x).obj Xo.univ.t.G).hom := show Smooth (pullback.snd _ _) from inferInstance
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj Xo.univ.t.G)
  have B := fun τ => (exists_eig_basis (c := c) hx0 hx τ).some
  obtain ⟨t', ⟨m⟩⟩ := exists_sab x Xo.univ.t
  obtain ⟨β, hβ⟩ := globalSections_rank_one_obj hT Xo.univ m
  obtain ⟨s, hs⟩ := locFrGen_of x m β hβ
  refine ⟨⟨x, hx0, fun τ i => gsvVec x xc (B τ i), fun τ i => gsv_tan hx _, fun τ i => (gsv_eig_iff hx τ _).2 (B τ i).2,
    fun τ w hw he => ?_, s, hs⟩, rfl⟩
  obtain ⟨cc, rfl⟩ := gsv_exists hx w hw
  let v : eigLat hx (fun a => (Over.pullback x).map (Xo.univ.t.act.act a)) fun a => algebraMap c.F L (embK c τ a) :=
    ⟨cc, (gsv_eig_iff hx τ _).1 he⟩
  have k : ∀ a, IsCombAt x (fun i => gsvVec x xc (B τ i)) a (gsvVec x xc cc) ↔ (B τ).equivFun v = a := fun a => by
    rw [gsv_comb_iff hx, ← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp [v]
  simp only [k]
  exact existsUnique_eq'

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.NumericalH1Condition
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

variable (Xo c) in

def CombAlg {n : ℕ} (ws : Fin n → Rul Xo c) (et : Rul Xo c) (nu : HeightOneSpectrum (𝓞 c.F) → ℝ) (c' : ℝ) :
    Prop :=
  ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v et ∧
    (v et ≠ ⊤ → (⨅ k, v (ws k)) ≤ (nu la : EReal) + (c' : EReal) * v et)

variable (c) in

def nuOf (nus : HeightOneSpectrum (𝓞 c.F) → ℝ) (la : HeightOneSpectrum (𝓞 c.F)) : ℝ :=
  (ramOverZ la : ℝ) * nus la

variable (c) in

def NumericalH1Condition (nus : HeightOneSpectrum (𝓞 c.F) → ℝ) (P s : ℝ) : Prop :=
  (∀ la, 0 ≤ nus la) ∧ (Function.support nus).Finite ∧
    (∑ᶠ la, (ramOverZ la : ℝ) * nus la * logNorm la) / (Module.finrank ℚ c.F : ℝ) ≤ P * s

def OrdTieOn (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop) : Prop :=
  ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)) (la : HeightOneSpectrum (𝓞 c.F)),
    IsNormDiscrete v → IsOver (K := c.F) v la →
    ∃ y : PtV Xo c cls (PY la) (lies la) la,
      (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
        (((ordC (δ Z v) v (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) =
          (((ramIdx (K := c.F) v la : ℤ) : ℝ) : EReal) * vAtV y f) ∧
      (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f = 0 →
        (∃ g ∈ sec Xo c a n, evC h Z g ≠ 0) → vAtV y f = ⊤)

theorem OrdTieOn.ordTie {h : GenFrEx Xo c} {δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ}
    {cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop} {PY : HeightOneSpectrum (𝓞 c.F) → Type}
    {lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop}
    (H : OrdTieOn h δ cls PY lies) : OrdTie h δ cls PY lies := fun Z v la hv ho =>
  let ⟨y, hy, _⟩ := H Z v la hv ho
  ⟨y, hy⟩

theorem one_le_ramIdx {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    {v : AddValuation Ω (WithTop ℤ)} {la : HeightOneSpectrum (𝓞 K)} (hv : IsNormDiscrete v)
    (ho : IsOver (K := K) v la) : 1 ≤ ramIdx (K := K) v la := by
  unfold ramIdx
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot la.ne_bot
  have hK : ((a : K)) ≠ 0 := by exact_mod_cast ha0
  have hne : v (algebraMap K Ω (a : K)) ≠ ⊤ := hv.1 _ ((map_ne_zero _).2 hK)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
  refine le_csInf ⟨n, a, ha, ha0, hn.symm⟩ ?_
  rintro m ⟨b, hb, _, hbm⟩
  have h1 := (ho b).2 hb
  rw [hbm] at h1
  have h0 : (0 : ℤ) < m := by exact_mod_cast h1
  omega

section H1

variable [Fintype (Comp Xo c)] (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nus : HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)

theorem height_H1_of_data {rU : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU) (hreg : regular₂ Xo c U)
    (hdL : Dom uL.1 uL.2) (hdE : Dom uet.1 uet.2) (hw : ∀ k, wR k ∈ cusp Xo c U uL.1 uL.2)
    (he : etR ∈ cusp Xo c U uet.1 uet.2) (hnz : NoCommonZero Xo c wR) (hetZ : NZAt h etR)
    (hwb : ∀ Z, evC h Z (wR (jc Z)) ≠ 0) (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2) (hcc : 0 ≤ cc)
    (hcomb : CombAlg Xo c wR etR (nuOf c nus) (cc / (2 * (i : ℝ))))
    (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop)
    (htie : OrdTieOn h δ cls PY lies) (hnu : NumericalH1Condition c nus PN (wsize (wtZ uL.1 uL.2))) :
    (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R
      (nuOf c nus) ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).FinitePlaceHyp := by
  classical
  refine ⟨fun la => mul_nonneg (Nat.cast_nonneg _) (hnu.1 la), ?_, hnu.2.2, ?_⟩
  · refine hnu.2.1.subset fun la hla => ?_
    rw [Function.mem_support] at hla ⊢
    intro h0
    apply hla
    show (ramOverZ la : ℝ) * nus la = 0
    rw [h0, mul_zero]
  · intro Z v la hadm hover
    show ((⨅ j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0},
        ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z) : ℤ) : ℝ) ≤
      (ramIdx (K := c.F) v la : ℝ) * nuOf c nus la +
        cc / (2 * (i : ℝ)) * (ordC (δ Z v) v ((i * g0) • wtZ ude.1 ude.2) (valC h uet.1 uet.2 etR Z) : ℝ)
    rw [← huet]
    have hv : IsNormDiscrete v := hadm.1
    obtain ⟨y, hty, hzero⟩ := htie Z v la hv hover
    obtain ⟨T', io, e, ho, z, _, eta, _, hq⟩ := y.2
    let y1 : PtV Xo c (trivialClassCondition Xo c) Unit (fun _ _ _ _ => True) la := PtV.mk la ho z trivial () trivial
    have hyv : vAtV y1 = vAtV y := funext fun g => by
      show y1.1.1 g = y.1.1 g
      rw [hq]
      rfl
    have hc' : (0 : ℝ) ≤ cc / (2 * (i : ℝ)) := div_nonneg hcc (by positivity)
    have hR := (hreg.1.2 ⟨uL, hdL⟩ ⟨uet, hdE⟩ (N + 1) (fun k => ⟨wR k, hw k⟩) ⟨etR, he⟩ (nuOf c nus)
      (cc / (2 * (i : ℝ))) hc' hnz (fun la' y0 => hcomb la' y0.1 y0.2)).1 la ⟨vAtV y1, y1, rfl⟩
    have hR' : 0 ≤ vAtV y etR ∧ (vAtV y etR ≠ ⊤ →
        (⨅ k, vAtV y (wR k)) ≤ ((nuOf c nus la : ℝ) : EReal) + ((cc / (2 * (i : ℝ)) : ℝ) : EReal) * vAtV y etR) := by
      rw [← hyv]
      exact hR
    have he1 : 1 ≤ ramIdx (K := c.F) v la := one_le_ramIdx hv hover
    have hepos : (0 : ℝ) < (ramIdx (K := c.F) v la : ℝ) := by
      exact_mod_cast (show (0 : ℤ) < ramIdx (K := c.F) v la by omega)
    have hE := (hty uet.1 uet.2 etR (cusp_le_sec Xo c U _ _ he) (hetZ Z))
    have htopE : vAtV y etR ≠ ⊤ := by
      intro htop
      rw [htop, EReal.mul_top_of_pos (by exact_mod_cast hepos)] at hE
      exact EReal.coe_ne_top _ hE
    obtain ⟨x, hx⟩ : ∃ x : ℝ, vAtV y etR = (x : EReal) :=
      ⟨_, (EReal.coe_toReal htopE (vAtV_ne_bot y etR)).symm⟩
    have hB := hR'.2 htopE
    rw [hx, ← EReal.coe_mul, ← EReal.coe_add] at hB
    rw [hx, ← EReal.coe_mul, EReal.coe_eq_coe_iff] at hE
    obtain ⟨k0, hk0⟩ : ∃ k0, vAtV y (wR k0) = ⨅ k, vAtV y (wR k) := exists_eq_ciInf_of_finite
    rw [← hk0] at hB
    have hk0Z : evC h Z (wR k0) ≠ 0 := by
      intro h0
      rw [hzero uL.1 uL.2 (wR k0) (cusp_le_sec Xo c U _ _ (hw k0)) h0
        ⟨wR (jc Z), cusp_le_sec Xo c U _ _ (hw (jc Z)), hwb Z⟩] at hB
      exact absurd hB (not_le.2 (EReal.coe_lt_top _))
    have hW := hty uL.1 uL.2 (wR k0) (cusp_le_sec Xo c U _ _ (hw k0)) hk0Z
    have htopW : vAtV y (wR k0) ≠ ⊤ := fun ht => by
      rw [ht] at hB
      exact absurd hB (not_le.2 (EReal.coe_lt_top _))
    obtain ⟨t, ht⟩ : ∃ t : ℝ, vAtV y (wR k0) = (t : EReal) :=
      ⟨_, (EReal.coe_toReal htopW (vAtV_ne_bot y _)).symm⟩
    rw [ht, ← EReal.coe_mul, EReal.coe_eq_coe_iff] at hW
    rw [ht, EReal.coe_le_coe_iff] at hB
    calc ((⨅ j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0},
          ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z) : ℤ) : ℝ)
        ≤ (ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR k0) Z) : ℝ) :=
          Int.cast_le.2 (ciInf_le (f := fun j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0} =>
            ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z)) (Set.finite_range _).bddBelow
            ⟨k0, valC_ne_zero (a := uL.1) (n := uL.2) hk0Z⟩)
      _ = (ramIdx (K := c.F) v la : ℝ) * t := hW
      _ ≤ (ramIdx (K := c.F) v la : ℝ) * (nuOf c nus la + cc / (2 * (i : ℝ)) * x) :=
          mul_le_mul_of_nonneg_left hB hepos.le
      _ = (ramIdx (K := c.F) v la : ℝ) * nuOf c nus la +
            cc / (2 * (i : ℝ)) * ((ramIdx (K := c.F) v la : ℝ) * x) := by ring
      _ = _ := by rw [← hE]

end H1

end Formalism.L2.Pj
end
end

