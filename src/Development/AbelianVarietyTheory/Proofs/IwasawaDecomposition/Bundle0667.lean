import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalFiniteTorsionSplitting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0649
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0594
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0650
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0633

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeneratingFramesComplete
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.RayEv.Transport
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TransportLimit

theorem val_frame {X Y : Scheme.{0}} {L : LB X} {p : Y ⟶ X} (t : Frame L p) (ht : t.IsGen) {j₀ : L.ι}
    (h₀ : ⊤ ≤ LB.wchart L (K := PUnit) (fun _ => p) (fun _ => j₀)) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val t r z J = gm (r ≫ p) z _ (L.g (J (r ≫ p)) j₀) * gm r z ⊤ (res h₀ (t.s (fun _ => j₀))) := by
  refine (gen_trans ht r z (hJ.mem _ r) (h₀ (show r z ∈ (⊤ : Y.Opens) from trivial))).trans
    (congrArg₂ (· * ·) ?_ (gm_res r z h₀ (show r z ∈ (⊤ : Y.Opens) from trivial) _).symm)
  simp only [trF, Fintype.prod_unique, zpow_one]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem gw_change (U : UnifPre I D A G) (e : ℕ) {Z : Scheme.{0}} (xe : Z ⟶ (thickObj R I e G).left) (z : Z)
    {p : Z ⟶ G.left} {q : Z ⟶ D.toPre.P.A.left} (hp : xe ≫ (fstG I e G).left = p)
    (hq : xe ≫ (U.gt e).pG.left = q) {j j' : D.toPre.P.L.ι} {k k' : U.LG.L.ι} (hj : q z ∈ D.toPre.P.L.U j)
    (hj' : q z ∈ D.toPre.P.L.U j') (hk : p z ∈ U.LG.L.U k) (hk' : p z ∈ U.LG.L.U k') :
    gw (U.w e) xe z j (fun _ => k) =
      gm q z _ (D.toPre.P.L.g j j') * (gm p z _ (U.LG.L.g k k'))⁻¹ * gw (U.w e) xe z j' (fun _ => k') := by
  subst hp hq
  have w := (isGen_iff _).1 (U.w_gen e) Z xe z j j' (fun _ => k) (fun _ => k') hj hj' (mem_pull.2 hk)
    (mem_pull.2 hk')
  rw [gm_pull_g _ _ xe z _ _ (mem_pull.2 hk) (mem_pull.2 hk')] at w
  exact w

theorem exists_limit_unit (U : UnifPre I D A G) {W : Type} [CommRing W] [IsLocalRing W] (φ : R →+* W)
    [IsAdicComplete (I.map φ) W] (x : Sp W ⟶ G.left) (hx : x ≫ G.hom = spMap φ) (b : Sp W ⟶ D.toPre.P.A.left)
    (hb : Lies U x b) {jL : U.LG.L.ι} {jM : D.toPre.P.L.ι} (hL : ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL)
    (hM : ⊤ ≤ b ⁻¹ᵁ D.toPre.P.L.U jM) :
    ∃ a : Γ(Sp W, ⊤)ˣ, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, gm r z ⊤ a * gw (U.w e) xe z jM (fun _ => jL) = 1 := by
  choose y hy using GlobalTheory.FormalValue.exists_lift_thick I G φ x hx
  have mL : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, (fstG I e G).left (xe z) ∈ U.LG.L.U jL := fun e Z r xe h z =>
    (congrArg (fun q => q z ∈ U.LG.L.U jL) h).mpr (hL (show r z ∈ (⊤ : (Sp W).Opens) from trivial))
  have mM : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, (U.gt e).pG.left (xe z) ∈ D.toPre.P.L.U jM := fun e Z r xe h z =>
    (congrArg (fun q => q z ∈ D.toPre.P.L.U jM) (hb e Z r xe h)).mpr
      (hM (show r z ∈ (⊤ : (Sp W).Opens) from trivial))
  let O : ∀ e, (thickObj R I e G).left.Opens := fun e =>
    (D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => jM) ⊓ (U.LG.L.pull (fstG I e G).left).U (fun _ => jL)
  let s : ∀ e, Γ((thickObj R I e G).left, O e)ˣ := fun e => (U.w e).s (fun _ => jM, fun _ => jL)
  have mO : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, xe z ∈ O e := fun e Z r xe h z =>
    ⟨mem_pull.2 (mM e Z r xe h z), mem_pull.2 (mL e Z r xe h z)⟩
  have ht : ∀ e, ⊤ ≤ y e ⁻¹ᵁ O e := fun e z _ => mO e _ _ _ (hy e) z
  have hc : ∀ e, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))
      (valR (y (e + 1)) (O (e + 1)) (s (e + 1)).val) = valR (y e) (O e) (s e).val := fun e => by
    have := isLocalRing_quotient_pow (ne_top_of_isHausdorff (I.map φ)) e
    have := GlobalTheory.FormalValue.fstG_mono (I := I) (G := G) (e + 1)
    have e₁ : thickTrans W (I.map φ) e ≫ y (e + 1) = y e ≫ thickMap R I e G := by
      rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, Category.assoc, hy,
        show thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left from GlobalTheory.thickMap_comp_fGl I e G, hy,
        ← Category.assoc, thickTrans_comp]
    apply toStkA_injective
    refine (GlobalTheory.FormalValue.toStkA_map_valR _ _ _ _ (ht _) _).trans
      (Eq.trans ?_ (GlobalTheory.FormalValue.toStkA_valR_eq_gs _ _ _ (ht _) _).symm)
    refine (gs_unit _ _ _ (mO (e + 1) _ (thickTrans W (I.map φ) e ≫ thick W (I.map φ) (e + 1)) _ (by
      rw [Category.assoc, hy, Category.assoc]) _) _).trans (Eq.trans ?_ (gs_unit _ _ _ (mO e _ _ _ (hy e) _) _).symm)
    refine congrArg Units.val ((congrArg (fun q => gm q _ (O (e + 1)) (s (e + 1))) e₁).trans ?_)
    exact GlobalTheory.FormalValue.wv_comp_thickMap e (y e) _ jM jL (mM e _ _ _ (hy e) _) (mL e _ _ _ (hy e) _)
  obtain ⟨a, ha⟩ := GlobalTheory.FormalValue.exists_unit_limit (I.map φ) _ hc fun e =>
    GlobalTheory.FormalValue.isUnit_valR _ _ (ht e) _
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom.toMonoidHom a, fun e Z r xe h z => ?_⟩
  obtain ⟨ρ, rfl⟩ := GlobalTheory.NormGen.exists_factor I φ e r (xe ≫ (thickObj R I e G).hom) (by
    rw [← hx, ← Category.assoc r, ← h, Category.assoc, Category.assoc]
    exact congrArg (xe ≫ ·) pullback.condition.symm)
  have := GlobalTheory.FormalValue.fstG_mono (I := I) (G := G) e
  obtain rfl : xe = ρ ≫ y e := by
    rw [← cancel_mono (fstG I e G).left, h, Category.assoc, Category.assoc, hy]
  apply Units.ext
  have H := congrArg (fun t => gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (W ⧸ I.map φ ^ (e + 1)))).inv.hom t)) (ha e)
  simp only [map_mul, map_one] at H
  rw [gs_mul ρ z ⊤ trivial, GlobalTheory.NormGen.gs_valR _ _ _ (ht e), gs_unit _ _ _ (mO e _ _ _ h z), gs_eq ρ z ⊤ trivial 1,
    map_one, map_one] at H
  refine Eq.trans (congrArg₂ (· * ·) ?_ rfl) H
  rw [← gs_unit _ z ⊤ trivial, ← GlobalTheory.NormGen.gs_valR ρ (thick W (I.map φ) e) ⊤ le_top]
  refine congrArg (fun t => gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (W ⧸ I.map φ ^ (e + 1)))).inv.hom t)) ?_
  have k := GlobalTheory.FormalValue.valR_spMap (Ideal.Quotient.mk (I.map φ ^ (e + 1))) (𝟙 (Sp W)) ⊤ le_top
    ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a.val)
  rw [GlobalTheory.NormGen.valR_id, Category.comp_id] at k
  exact k

theorem exists_frRel : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (W : Type) [CommRing W] [IsLocalRing W] (φ : R →+* W) [IsAdicComplete (I.map φ) W] (x' : Sp W ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ b : Sp W ⟶ D.toPre.P.A.left, Lies U x' b → ∃ (g' : Frame U.LG.L x') (g : Frame D.toPre.P.L b), g'.IsGen ∧ g.IsGen ∧ FrRel U x' b g' g := by
  intro R _ _ I D A G _ _ U W _ _ φ _ x' hx b hb
  obtain ⟨jL, hjL⟩ := exists_chart U.LG.isLB (x' (cpt W))
  obtain ⟨jM, hjM⟩ := exists_chart D.toPre.P.isLB (b (cpt W))
  replace hjL := (top_le_iff_cpt (A := W) x' _).2 hjL
  replace hjM := (top_le_iff_cpt (A := W) b _).2 hjM
  obtain ⟨a, ha⟩ := exists_limit_unit U φ x' hx b hb hjL hjM
  obtain ⟨ν', hν'⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := W) U.LG.L U.LG.isLB (K := PUnit) (fun _ => x') (fun _ => 1)
  obtain ⟨ν, hν⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := W) D.toPre.P.L D.toPre.P.isLB (K := PUnit) (fun _ => b) (fun _ => 1)
  have tL : ⊤ ≤ LB.wchart U.LG.L (K := PUnit) (fun _ => x') (fun _ => jL) := fun y _ =>
    Set.mem_iInter.2 fun _ => hjL (show y ∈ (⊤ : (Sp W).Opens) from trivial)
  have tM : ⊤ ≤ LB.wchart D.toPre.P.L (K := PUnit) (fun _ => b) (fun _ => jM) := fun y _ =>
    Set.mem_iInter.2 fun _ => hjM (show y ∈ (⊤ : (Sp W).Opens) from trivial)
  refine ⟨GlobalTheory.UU.scaleGen (res tL (ν'.s fun _ => jL))⁻¹ ν', GlobalTheory.UU.scaleGen (a⁻¹ * (res tM (ν.s fun _ => jM))⁻¹) ν,
    GlobalTheory.UU.scaleGen_isGen _ hν', GlobalTheory.UU.scaleGen_isGen _ hν, ?_⟩
  intro e Z r y hy z JM JL hJM hJL
  have hyb := hb e Z r y hy
  have m : ∀ {X : Scheme.{0}} {f : Sp W ⟶ X} {O : X.Opens}, ⊤ ≤ f ⁻¹ᵁ O → (r ≫ f) z ∈ O := fun h =>
    h (show r z ∈ (⊤ : (Sp W).Opens) from trivial)
  have v₁ := GlobalTheory.UU.val_scaleGen (res tL (ν'.s fun _ => jL))⁻¹ ν' r hJL
  rw [val_frame ν' hν' tL r z hJL] at v₁
  have v₂ := GlobalTheory.UU.val_scaleGen (a⁻¹ * (res tM (ν.s fun _ => jM))⁻¹) ν r hJM
  rw [val_frame ν hν tM r z hJM] at v₂
  have w₁ : wVal U e z JM JL y = gm (r ≫ b) z _ (D.toPre.P.L.g (JM (r ≫ b)) jM) *
      (gm (r ≫ x') z _ (U.LG.L.g (JL (r ≫ x')) jL))⁻¹ * gw (U.w e) y z jM (fun _ => jL) :=
    (congrArg₂ (fun j k => gw (U.w e) y z (JM j) (fun _ => JL k)) hyb hy).trans
      (gw_change U e y z hy hyb (hJM _) (m hjM) (hJL _) (m hjL))
  rw [eq_inv_of_mul_eq_one_right (ha e Z r y hy z)] at w₁
  rw [v₁, v₂, w₁]
  simp only [map_mul, map_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TransportLimit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLagrangianDualPairInCoisotropic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open Module

theorem exists_lagrangian_dual_in_coisotropic : ∀ (r : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (W : Submodule ℝ (Fin r → ℝ)), Mᵀ = -M → M.det ≠ 0 → (∀ v : Fin r → ℝ, (∀ w ∈ W, v ⬝ᵥ M *ᵥ w = 0) → v ∈ W) → ∃ (d : ℕ) (e f : Fin d → Fin r → ℝ), (∀ i, e i ∈ W) ∧ (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) ∧ (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) ∧ Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ := by
  classical
  intro r M W hskew hdet hW
  set B : LinearMap.BilinForm ℝ (Fin r → ℝ) := Matrix.toBilin' M with hBdef
  have hB : ∀ v w, B v w = v ⬝ᵥ M *ᵥ w := fun v w => by
    simp [hBdef, Matrix.toBilin'_apply']
  have hskewB : ∀ v w, B v w = - B w v := by
    intro v w
    rw [hB, hB, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hskew, Matrix.neg_mulVec,
      neg_dotProduct, dotProduct_comm]
  have hBalt : ∀ v, B v v = 0 := fun v => by have := hskewB v v; linarith
  have hrefl : B.IsRefl := fun x y h => by rw [hskewB, h, neg_zero]
  have hnd : B.Nondegenerate := LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' M hdet
  let P : ℕ → Prop := fun n => ∃ L : Submodule ℝ (Fin r → ℝ), L ≤ W ∧
    (∀ x ∈ L, ∀ y ∈ L, B x y = 0) ∧ finrank ℝ L = n
  have P0 : P 0 := ⟨⊥, bot_le, by simp, finrank_bot ℝ _⟩
  obtain ⟨L, hLW, hLiso, hLdim⟩ : P (Nat.findGreatest P r) := Nat.findGreatest_spec (Nat.zero_le _) P0
  have hmax : ∀ v ∈ W, (∀ l ∈ L, B v l = 0) → v ∈ L := by
    intro v hvW hvL
    by_contra hv
    have hlt : L < L ⊔ Submodule.span ℝ {v} := lt_of_le_of_ne le_sup_left (fun h => hv (by
      rw [h]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)))
    have hiso : ∀ x ∈ L ⊔ Submodule.span ℝ {v}, ∀ y ∈ L ⊔ Submodule.span ℝ {v}, B x y = 0 := by
      intro x hx y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
      obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hb'
      have h1 := hLiso a ha a' ha'
      have h2 := hvL a' ha'
      have h3 : B a v = 0 := by rw [hskewB, hvL a ha, neg_zero]
      have h4 := hBalt v
      simp [map_add, map_smul, h1, h2, h3, h4]
    have hle : L ⊔ Submodule.span ℝ {v} ≤ W :=
      sup_le hLW (by rw [Submodule.span_le]; simpa using hvW)
    have hP : P (finrank ℝ ↥(L ⊔ Submodule.span ℝ {v})) := ⟨_, hle, hiso, rfl⟩
    have h5 := Nat.le_findGreatest (by simpa using Submodule.finrank_le (L ⊔ Submodule.span ℝ {v})) hP
    have h6 := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hWo : B.orthogonal W ≤ L := by
    intro x hx
    have hxW : x ∈ W := hW x (fun w hw => by rw [← hB, hskewB, hx w hw, neg_zero])
    exact hmax x hxW (fun l hl => by rw [hskewB, hx l (hLW hl), neg_zero])
  let b := Module.finBasis ℝ L
  let e : Fin (finrank ℝ L) → Fin r → ℝ := fun i => ((b i : L) : Fin r → ℝ)
  have heL : ∀ i, e i ∈ L := fun i => (b i).2
  have hext : ∀ (φ : (Fin r → ℝ) →ₗ[ℝ] ℝ), (∀ j, φ (e j) = 0) → ∀ l ∈ L, φ l = 0 := by
    intro φ hφ l hl
    have : φ ∘ₗ L.subtype = 0 := b.ext (fun j => by simpa using hφ j)
    simpa using LinearMap.congr_fun this ⟨l, hl⟩
  let φ : (Fin r → ℝ) →ₗ[ℝ] (Fin (finrank ℝ L) → ℝ) := LinearMap.pi (fun j => B.flip (e j))
  have hφ : ∀ v j, φ v j = B v (e j) := fun v j => rfl
  have hker : LinearMap.ker φ = B.orthogonal L := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h l hl
      have h' := hext (B v) (fun j => by rw [← hφ, h]; rfl) l hl
      rw [hskewB, h', neg_zero]
    · intro h
      funext j
      rw [Pi.zero_apply, hφ, hskewB, h _ (heL j), neg_zero]
  have hrange : LinearMap.range φ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    rw [hker, LinearMap.BilinForm.finrank_orthogonal hnd] at h1
    have h2 : finrank ℝ L ≤ r := by simpa using Submodule.finrank_le L
    simp only [Module.finrank_fin_fun] at h1 ⊢
    omega
  have hsurj : ∀ y, ∃ x, φ x = y := fun y => by
    have : y ∈ LinearMap.range φ := by rw [hrange]; trivial
    exact this
  choose f hf using fun i : Fin (finrank ℝ L) => hsurj (Pi.single i 1)
  have hfe : ∀ i j, B (f i) (e j) = if i = j then 1 else 0 := by
    intro i j
    rw [← hφ, hf i, Pi.single_apply]
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · simp [h, Ne.symm h]
  refine ⟨finrank ℝ L, e, f, fun i => hLW (heL i),
    fun i j => by rw [← hB]; exact hLiso _ (heL i) _ (heL j),
    fun i j => by rw [← hB]; exact hfe i j, ?_⟩
  set U := Submodule.span ℝ (Set.range (Sum.elim e f)) with hU
  have hUo : B.orthogonal U = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hve : ∀ j, B (e j) v = 0 := fun j => hv _ (Submodule.subset_span ⟨Sum.inl j, rfl⟩)
    have hvf : ∀ i, B (f i) v = 0 := fun i => hv _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)
    have hvL : ∀ l ∈ L, B v l = 0 := hext (B v) (fun j => by rw [hskewB, hve j, neg_zero])
    have hvW : v ∈ W := by
      rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl W]
      intro x hx
      rw [hskewB, hvL x (hWo hx), neg_zero]
    have hvL' : v ∈ L := hmax v hvW hvL
    have hv' : v = ∑ j, b.repr ⟨v, hvL'⟩ j • e j := by
      have := congrArg Subtype.val (b.sum_repr ⟨v, hvL'⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    have hc : ∀ i, b.repr ⟨v, hvL'⟩ i = 0 := by
      intro i
      have h := hvf i
      rw [hv', map_sum] at h
      simpa [map_smul, hfe] using h
    have h0 : (⟨v, hvL'⟩ : L) = 0 := b.repr.injective (by ext i; simp [hc])
    simpa using congrArg Subtype.val h0
  have hdimU := LinearMap.BilinForm.finrank_orthogonal hnd U
  rw [hUo, finrank_bot] at hdimU
  apply Submodule.eq_top_of_finrank_eq
  have := Submodule.finrank_le U
  simp only [Module.finrank_fin_fun] at hdimU this ⊢
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalFiniteTorsionSplittingStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_finite_torsion_splitting : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R] (x : Sp R ⟶ X) (q : ℕ), q ≠ 0 → SplitTors t x q → ∀ 𝔭 : Ideal R, 𝔭.IsPrime → ∃ (f : R) (B : Type) (_ : CommRing B) (_ : Algebra (Localization.Away f) B) (u : Over.mk (spMap (algebraMap (Localization.Away f) B) ≫ spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ t.G), f ∉ 𝔭 ∧ IsFinPart t (spMap (algebraMap R (Localization.Away f)) ≫ x) q u ∧ ∀ (k : Type) [Field k] (φ : Localization.Away f →+* k), RingHom.ker (φ.comp (algebraMap R (Localization.Away f))) = 𝔭 → ∀ w : Over.mk (spMap φ ≫ spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ t.G, w ^ q = 1 → Thru t u.left φ w.left := by
  first | exact @GlobalTheory.SplitFinitePart.exists_finite_part | exact GlobalTheory.SplitFinitePart.exists_finite_part | (intros; apply GlobalTheory.SplitFinitePart.exists_finite_part <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalFlagCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_flag_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (σ : F →+* ℂ) (y : Y.Y.X), ∃ (U : Y.Y.X.Opens) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ) (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (Fr : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(Y.Y.X, U)), y ∈ U ∧ LogKS.chart V ≫ genStr Z = spMap φ ∧ (∀ p : Y.Y.pts σ, p ∈ ptsIn Y.Y.str σ U → Y.down p ∈ ptsIn (genStr Z) (embOf e σ) V.1) ∧ (∀ y' ∈ U, ∀ τ i, (Y.gr τ i).IsEqn y' (t τ i)) ∧ ∀ (p : Y.Y.pts σ) (hp : p ∈ ptsIn Y.Y.str σ U), ∃ (hv : Y.down p ∈ ptsIn (genStr Z) (embOf e σ) V.1) (g f : Y.FrameAt p), Y.Adapted p t g 1 ∧ Fr.IsMap (evHom hv) f ∧ ∀ τ, f.co g τ = (A τ).map (evHom hp) := by
  first | exact @GlobalTheory.ShFam.FlagFrames.exists_frames_nhds | exact GlobalTheory.ShFam.FlagFrames.exists_frames_nhds | (intros; apply GlobalTheory.ShFam.FlagFrames.exists_frames_nhds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonnegCombOfMemPsdCone
section
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan.ConeSpan

theorem exists_margin {ι : Type} [Fintype ι] (M : ι → ι → ℝ)
    (hM : ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * M i j) :
    ∃ η : ℝ, 0 < η ∧ ∀ E : ι → ι → ℝ, (∀ i j, |E i j| ≤ η) → ∀ c : ι → ℝ, c ≠ 0 →
      0 < ∑ i, ∑ j, c i * c j * (M i j + E i j) := GlobalTheory.T.exists_margin_quadForm_pos_of_perturbation M hM

theorem exists_rat_span {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (B : L →ₗ[ℤ] L →ₗ[ℤ] ℝ) : ∃ (n : ℕ) (w : Fin n → ℝ) (Q : Fin n → LinearMap.BilinForm ℤ L),
      B = ∑ j, w j • toReal (Q j) ∧ ∀ j, ∃ g : ℝ →+ ℝ, ∀ y z, (Q j y z : ℝ) = g (B y z) := GlobalTheory.T.exists_realBilinForm_eq_sum_additive_image_intForms B

theorem free_finite_int (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O] (X₁ : Type)
    [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] [Module.Projective O X₁] :
    Module.Free ℤ X₁ ∧ Module.Finite ℤ X₁ := by
  have : Module.Finite ℤ X₁ := Module.Finite.trans O X₁
  refine ⟨?_, this⟩
  have : Module.IsTorsionFree O X₁ := Module.Flat.isTorsionFree
  have : Module.IsTorsionFree ℤ X₁ :=
    Module.IsTorsionFree.comap (S := O) (Int.castRingHom O)
      (fun r hr => IsRegular.of_ne_zero (by
        intro h0
        have : r = 0 := by simpa using h0
        subst this
        exact (not_isRegular_zero (R := ℤ)) hr))
      (fun r m => Int.cast_smul_eq_zsmul O r m)
  exact Module.free_of_finite_type_torsion_free'

theorem nonneg_of_near {ι L : Type} [Fintype ι] [AddCommGroup L] (b : Module.Basis ι ℤ L)
    {B₁ : L →ₗ[ℤ] L →ₗ[ℤ] ℝ} (h : IsPosDef B₁) : ∃ η : ℝ, 0 < η ∧ ∀ (P : LinearMap.BilinForm ℤ L) (D : ℝ), 0 < D →
      (∀ i j, |(P (b i) (b j) : ℝ) / D - B₁ (b i) (b j)| ≤ η) → ∀ x, 0 ≤ P x x := by
  obtain ⟨η, hη, hE⟩ := exists_margin (fun i j => B₁ (b i) (b j)) ((isPosDef_iff_basis b B₁).1 h)
  refine ⟨η, hη, fun P D hD hP x => ?_⟩
  have hP' : IsPosDef (toReal P) := (isPosDef_iff_basis b _).2 fun c hc => by
    have h1 := hE (fun i j => (P (b i) (b j) : ℝ) / D - B₁ (b i) (b j)) hP c hc
    simp only [add_sub_cancel] at h1
    simp only [toReal_apply]
    have e : ∑ i, ∑ j, c i * c j * ((P (b i) (b j) : ℝ) / D) = (∑ i, ∑ j, c i * c j * (P (b i) (b j) : ℝ)) / D := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e] at h1
    exact (div_pos_iff_of_pos_right hD).1 h1
  have := hP'.nonneg x
  simpa using this

theorem exists_nonneg_comb_of_mem_psdCone (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ)
    (hB : B ∈ psdCone bar X) : ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ),
      (∀ i, γ i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ γ i y y) ∧ (∀ i, 0 ≤ c i) ∧ B = ∑ i, c i • toReal (γ i) := by
  obtain ⟨X₁, _, _, _, r, B₁, hr, hB₁, hpos, hBr⟩ := hB
  have : Module.Finite O X₁ := Module.Finite.of_surjective r hr
  obtain ⟨_, _⟩ := free_finite_int O X₁
  let b := Module.Free.chooseBasis ℤ X₁
  obtain ⟨η, hη, hnear⟩ := nonneg_of_near b hpos
  obtain ⟨n, w, Q, hw, hg⟩ := exists_rat_span B₁
  have hwv : ∀ y z, B₁ y z = ∑ k, w k * (Q k y z : ℝ) := fun y z => by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hw y z
  have hQ : ∀ k, Q k ∈ balForms bar X₁ := fun k => by
    obtain ⟨g, hg⟩ := hg k
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · exact_mod_cast (hg y z).trans ((congrArg g (hB₁.1 y z)).trans (hg z y).symm)
    · exact_mod_cast (hg _ _).trans ((congrArg g (hB₁.2 a y z)).trans (hg _ _).symm)
  set K : ℝ := ∑ k, ∑ i, ∑ j, |(Q k (b i) (b j) : ℝ)| with hK
  have hKsum : ∀ i j, ∑ k, |(Q k (b i) (b j) : ℝ)| ≤ K := fun i j => Finset.sum_le_sum fun k _ =>
    (Finset.single_le_sum (f := fun j => |(Q k (b i) (b j) : ℝ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, |(Q k (b i) (b j) : ℝ)|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  have hKle : ∀ k i j, |(Q k (b i) (b j) : ℝ)| ≤ K := fun k i j =>
    (Finset.single_le_sum (f := fun k => |(Q k (b i) (b j) : ℝ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ k)).trans (hKsum i j)
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨D, hD⟩ := exists_nat_gt (2 * (n + 1) * K / η)
  have hDpos : (0 : ℝ) < D := lt_of_le_of_lt (by positivity) hD
  have hDK : 2 * (n + 1) * K ≤ D * η := by rw [div_lt_iff₀ hη] at hD; linarith
  set a : Fin n → ℤ := fun k => ⌊(D : ℝ) * w k⌋ with ha
  set δ : Fin n → ℝ := fun k => D * w k - a k with hδ
  have hδ0 : ∀ k, 0 ≤ δ k := fun k => sub_nonneg.2 (Int.floor_le _)
  have hδ1 : ∀ k, δ k ≤ 1 := fun k => by
    have := Int.lt_floor_add_one ((D : ℝ) * w k)
    simp only [hδ, ha]; linarith
  set R : LinearMap.BilinForm ℤ X₁ := ∑ k, a k • Q k with hR
  have hRv : ∀ y z, (R y z : ℝ) = D * B₁ y z - ∑ k, δ k * (Q k y z : ℝ) := fun y z => by
    simp only [hR, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul, hwv,
      Finset.mul_sum, ← Finset.sum_sub_distrib, hδ]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hSb : ∀ i j, |∑ k, δ k * (Q k (b i) (b j) : ℝ)| ≤ K := fun i j =>
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun k _ => by
      rw [abs_mul, abs_of_nonneg (hδ0 k)]
      exact mul_le_of_le_one_left (abs_nonneg _) (hδ1 k)).trans (hKsum i j))
  have hRnn : ∀ x, 0 ≤ R x x := hnear R D hDpos fun i j => by
    rw [hRv, show (D * B₁ (b i) (b j) - ∑ k, δ k * (Q k (b i) (b j) : ℝ)) / D - B₁ (b i) (b j) =
      -(∑ k, δ k * (Q k (b i) (b j) : ℝ)) / D by field_simp; ring, abs_div, abs_neg, abs_of_pos hDpos,
      div_le_iff₀ hDpos]
    nlinarith [hSb i j]
  let N : ℤ := n + 1
  have hQnn : ∀ k x, 0 ≤ (R + N • Q k) x x := fun k => hnear _ D hDpos fun i j => by
    have e : ((R + N • Q k) (b i) (b j) : ℝ) / D - B₁ (b i) (b j) =
        (N * (Q k (b i) (b j) : ℝ) - ∑ l, δ l * (Q l (b i) (b j) : ℝ)) / D := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul, hRv]
      field_simp; ring
    rw [e, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
    have h1 := abs_sub (N * (Q k (b i) (b j) : ℝ)) (∑ l, δ l * (Q l (b i) (b j) : ℝ))
    rw [abs_mul] at h1
    have h2 : |(N : ℝ)| = n + 1 := by simp [N]; positivity
    rw [h2] at h1
    nlinarith [hSb i j, hKle k i j]
  let γ₁ : Fin (n + 1) → LinearMap.BilinForm ℤ X₁ := Fin.cons R fun k => R + N • Q k
  let c : Fin (n + 1) → ℝ := Fin.cons ((1 + ∑ k, (1 - δ k)) / (N * D)) fun k => δ k / (N * D)
  have hN : (0 : ℝ) < N := by simp [N]; positivity
  refine ⟨n + 1, fun i => pull r (γ₁ i), c, fun i => pull_mem r ?_, fun i y => ?_, fun i => ?_, ?_⟩
  · refine Fin.cases ?_ (fun k => ?_) i
    · exact (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hQ k) : R ∈ _)
    · show R + N • Q k ∈ _
      exact Submodule.add_mem _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hQ k))
        (Submodule.smul_mem _ _ (hQ k))
  · simp only [pull_apply]
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hRnn _
    · exact hQnn k _
  · refine Fin.cases ?_ (fun k => ?_) i
    · refine div_nonneg (add_nonneg zero_le_one (Finset.sum_nonneg fun k _ => sub_nonneg.2 (hδ1 k))) (by positivity)
    · exact div_nonneg (hδ0 k) (by positivity)
  · refine LinearMap.ext₂ fun y z => ?_
    simp only [hBr, LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, pull_apply, smul_eq_mul,
      Fin.sum_univ_succ, γ₁, c, Fin.cons_zero, Fin.cons_succ, LinearMap.add_apply, Int.cast_add, Int.cast_mul]
    rw [hRv]
    set u := B₁ (r y) (r z)
    set S := ∑ k, δ k * (Q k (r y) (r z) : ℝ)
    have e1 : ∑ k, δ k / (N * D) * (D * u - S + N * (Q k (r y) (r z) : ℝ)) =
        (∑ k, δ k) * (D * u - S) / (N * D) + S / D := by
      rw [Finset.sum_mul, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp
    have e2 : ∑ k, (1 - δ k) = n - ∑ k, δ k := by
      rw [Finset.sum_sub_distrib]; simp
    rw [e1, e2]
    have hN' : (N : ℝ) = n + 1 := by simp [N]
    rw [hN']
    field_simp
    ring

end GlobalTheory.PolFan.ConeSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPluckerFlagEmbeddingOfProjectiveBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pluckerFlagEmbedding_of_projective_base : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → IsCover β s V α c D → ∃ (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsPlk β s V α c p0 p h := by
  first | exact @GlobalTheory.FlagEmb.exists_isPlk | exact GlobalTheory.FlagEmb.exists_isPlk | (intros; apply GlobalTheory.FlagEmb.exists_isPlk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPointOfIntegralPointStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_of_integral_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀) (C : SCF p) (z : Sp ↥(intO ↥C.S) ⟶ Z.X), Set.range (spMap (intO ↥C.S).subtype ≫ z) ⊆ Z.opn → ∃ P : PointsOfFlagModel.PtC (Y Z.i) C, z ≫ Z.π = P.yt := by
  first | exact @GlobalTheory.ModelPt.exists_ptC | exact GlobalTheory.ModelPt.exists_ptC | (intros; apply GlobalTheory.ModelPt.exists_ptC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedUniformisationPolarisedTripleStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_uniformisation_polarisedTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V], CDvr V → ∀ ϖ : V, Irreducible ϖ → ∀ (t : SAB H (Sp V)), PolAt t (jK V) →
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V'),
      CDvr V' ∧ Function.Injective f ∧ IsLocalHom f ∧ Irreducible (f ϖ) ∧
      ∃ (t' : SAB H (Sp V')) (_ : SABMap t' t (spMap f)), Nonempty (PELUnif (maximalIdeal V') t') := by
  first | exact @GlobalTheory.TorRef.exists_unif_unram | exact GlobalTheory.TorRef.exists_unif_unram | (intros; apply GlobalTheory.TorRef.exists_unif_unram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMapStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expCoordinates_tangentField_holomorphic_periodMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) (n : ℕ) (B : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → ((Fu.Di i).La →+ (Fin g → ℂ))) (p : (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c)) (hu : ∀ b, Fu.u i (P b) = p b ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (V : (gen Z).affineOpens) (v : Sp (DualNumber Γ(gen Z, V.1)) ⟶ Z.t.G.left), IsOpen B → (∀ b, IsPeriod (Fu.Di i) ty (P b)) → (∀ a, DifferentiableOn ℂ (fun b => P b a) B) → (∀ b, p b ≫ pullback.snd _ _ = spMap σ) → IsTanAtG Z.t (LogKS.chart V ≫ genι Z) v → ∃ W : (Fin n → ℂ) → (Fin g → ℂ), DifferentiableOn ℂ W {b ∈ B | ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1} ∧ ∀ b ∈ B, ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1), y.1 = p b ≫ Z.jQ → IsDerivAt0 (fun z => GlobalTheory.ShFam.Hor.LogCh.liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b) (spMap (Formalism.L2.Pj.dualMap (evHom hy)) ≫ v) := by
  first | exact @GlobalTheory.ModelExpCoord.coord_holomorphic | exact GlobalTheory.ModelExpCoord.coord_holomorphic | (intros; apply GlobalTheory.ModelExpCoord.coord_holomorphic <;> assumption)
end

