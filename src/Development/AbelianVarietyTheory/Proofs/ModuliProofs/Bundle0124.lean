import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0104
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfInvGenOfInvariants
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecOnNonvanishingOfTameQuotient
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ResidueFieldMapFiniteSeparableOfTame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankSectionsPullbackMulByNTwists
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecRelAmplePowDivNeZero
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AmpleDivSec

open LBGerm GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out

variable {X : Scheme.{0}}

def invLB (L : LB X) : LB X := ⟨L.1, L.U, fun i j => (L.g i j)⁻¹⟩

theorem isLB_invLB {L : LB X} (hL : L.IsLB) : (invLB L).IsLB where
  cover := hL.cover
  g_self i := by
    have h := congrArg (·⁻¹) (hL.g_self i)
    simp only [inv_one, ← map_inv] at h
    exact h
  cocycle i j k := by
    have h := congrArg (·⁻¹) (hL.cocycle i j k)
    simp only [mul_inv, ← map_inv] at h
    exact h

theorem exists_sec_div (L M : LB X) (n t : ℕ) (u : LB.Sec (tw (invLB L) (lbPow M n) (t : ℤ))) :
    ∃ s : (LB.div (lbPow M (n * t)) L).Sec, nonzeroLocus u ≤ nonzeroLocus s := by
  have le : ∀ p : (PUnit → M.ι) × L.ι, powChart M p.1 ⊓ L.U p.2 ≤ L.U p.2 ⊓ powChart M p.1 :=
    fun p y hy => ⟨hy.2, hy.1⟩
  let F : ∀ p : (PUnit → M.ι) × L.ι, Γ(X, powChart M p.1 ⊓ L.U p.2) := fun p =>
    resG X (le p) (show Γ(X, L.U p.2 ⊓ powChart M p.1) from u.f (p.2, p.1))
  have hF : ∀ (y : X) (p : (PUnit → M.ι) × L.ι), y ∈ powChart M p.1 ⊓ L.U p.2 → gs (𝟙 X) y _ (F p) =
      gs (𝟙 X) y _ (u.f (p.2, p.1)) := fun y p hy => gs_res (𝟙 X) y (le p) hy _
  refine ⟨secOfGerm (M := LB.div (lbPow M (n * t)) L) F fun y p q hp hq => ?_, fun y hy => ?_⟩
  · have e₁ := gs_compat u (𝟙 X) y (j := (p.2, p.1)) (j' := (q.2, q.1)) (le p hp) (le q hq)
    have e₂ := TwistGen.gm_tw_g (invLB L) (lbPow M n) t y (p.2, p.1) (q.2, q.1) (le p hp) (le q hq)
    have e₃ := gm_lbPow_g (L := M) n (𝟙 X) y p.1 q.1 hp.1 hq.1
    have e₄ := gm_lbPow_g (L := M) (n * t) (𝟙 X) y p.1 q.1 hp.1 hq.1
    have e₅ := gm_div L (lbPow M (n * t)) (𝟙 X) y p q ⟨hp, hq⟩
    have e₆ : gm (𝟙 X) y ((invLB L).U p.2 ⊓ (invLB L).U q.2) ((invLB L).g p.2 q.2) =
        (gm (𝟙 X) y (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹ := map_inv _ _
    rw [e₄] at e₅
    dsimp only at e₂
    rw [e₃, e₆] at e₂
    refine (hF y p hp).trans (e₁.trans (congrArg₂ (· * ·) (e₂.trans ?_) (hF y q hq).symm))
    refine Eq.trans ?_ (congrArg Units.val e₅).symm
    rw [Units.val_mul, pow_mul, _root_.mul_comm]
    simp only [Units.val_pow_eq_pow_val]
  · obtain ⟨p, hp⟩ := exists_chart_of_mem_nonzeroLocus hy
    have hp' : y ∈ powChart M p.2 ⊓ L.U p.1 := ⟨hp.2, hp.1⟩
    refine (mem_nonzeroLocus_iff_isUnit (M := LB.div (lbPow M (n * t)) L) _ (k := (p.2, p.1)) hp').2 ?_
    exact (congrArg IsUnit (hF y (p.2, p.1) hp')).mpr ((mem_nonzeroLocus_iff_isUnit u hp).1 hy)

theorem exists_sec_div_mem {L M : LB X} (hL : L.IsLB) (hM : IsAmpleLB M) (x : X) :
    ∃ (a : ℕ) (s : (LB.div (lbPow M a) L).Sec), 1 ≤ a ∧ x ∈ nonzeroLocus s := by
  have := hM.compactSpace
  have := hM.quasiSeparatedSpace
  obtain ⟨n, hn, σ, hx, ha⟩ := hM.exists_affine x
  obtain ⟨V, N, hV, h⟩ := TwistGen.exists_nhds (isLB_invLB hL) (isLB_lbPow hM.isLB n) σ ha x hx
  obtain ⟨u, hu⟩ := h 1
  obtain ⟨s, hs⟩ := exists_sec_div L M n (N + 1) u
  exact ⟨_, s, Nat.mul_pos hn (Nat.succ_pos N), hs (hu hV)⟩

theorem exists_sec_pow_div_ne_zero : ∀ (K : Type) [Field K] (A : Over (Sp K)) (L M : LB A.left), IsProper A.hom → Nonempty A.left → L.IsLB → M.IsLB → Out.RelAmple A M → ∃ (a : ℕ) (s : (LB.div (lbPow M a) L).Sec), 1 ≤ a ∧ ∃ j, s.f j ≠ 0 := by
  intro K _ A L M _ ⟨x⟩ hL hM hA
  obtain ⟨a, s, ha, hx⟩ := exists_sec_div_mem hL (isAmpleLB_of_relAmple_of_isAffine A hM hA) x
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  refine ⟨a, s, ha, j, fun h => ?_⟩
  rw [h, Scheme.basicOpen_zero] at hj
  exact hj

end GlobalTheory.AmpleDivSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianDescentTameQuotient
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem fixes_iff_fixes_image {X Y T : Scheme.{0}} (p : Y ⟶ X) (r : X ⟶ X) (q : Y ⟶ Y) (y : T ⟶ Y)
    (w : q ≫ p = p ≫ r)
    (h : (y ≫ p) ≫ r = y ≫ p → pullback.fst p (y ≫ p) ≫ q = pullback.fst p (y ≫ p)) :
    y ≫ q = y ↔ (y ≫ p) ≫ r = y ≫ p := by
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · rw [Category.assoc, ← w, ← Category.assoc, hy]
  · have := pullback.lift y (𝟙 _) (Category.id_comp _).symm ≫= h hy
    rwa [pullback.lift_fst_assoc, pullback.lift_fst] at this

theorem exists_sab_descent_of_tame_quotient :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (R : Type) [CommRing R] (X X' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (π : X ⟶ X') (t : SAB H X) (s : X ⟶ Sp R) (τ : Γ →* Aut t.G.left) (mu : ∀ g, SABMap t t (ρ g).hom), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsFinite π → IsQProjOver (t.G.hom ≫ s) → (IsReduced X ∧ genericPoints X ⊆ abLocus t.G) → (∀ g, (mu g).φ = (τ g).hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).hom = x → pullback.fst t.G.hom x ≫ (τ g).hom = pullback.fst t.G.hom x) → ∃ (t' : SAB H X') (ν : SABMap t t' π), (∀ g, (τ g).hom ≫ ν.φ = ν.φ) ∧ (Good t → PushInvertible t.G t.PP.L → Good t') := by
  intro E _ _ _ H Γ _ _ R _ X X' _ ρ π t s τ mu hQ hfin hqp hga hmu htame hfib
  have hsemi := t.semi
  have hcart (g : Γ) : IsGrpPullback t.G t.G (ρ g).hom (τ g).hom := hmu g ▸ (mu g).cart
  have hw (g : Γ) : (τ g).hom ≫ t.G.hom = t.G.hom ≫ (ρ g).hom := (hcart g).1.w
  have hact (g : Γ) (c) : (t.act.act c).left ≫ (τ g).hom = (τ g).hom ≫ (t.act.act c).left :=
    hmu g ▸ (mu g).act c
  have he (g : Γ) : eSec t.G ≫ (τ g).hom = (ρ g).hom ≫ eSec t.G := by
    have := (mu g).cm.e_comm
    rw [(mu g).base] at this
    rw [← hmu g]
    exact this
  have hL (g : Γ) : LBIso t.PP.L (t.PP.L.pull (τ g).hom) := by
    obtain ⟨w, hw, -⟩ := (mu g).lin
    rw [← hmu g]
    exact ⟨w, hw⟩
  have hsec : eSec t.G ≫ t.G.hom = 𝟙 X := Over.w (η[t.G])
  have hgi : GeometricallyIntegral t.G.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hsemi.smooth hsemi.geomConnected
  obtain ⟨-, hsurj, -⟩ := quotient_isIntegral_surjective_orbits Γ X X' ρ π hQ
  obtain ⟨G', φ, hpb, hsm, hinv⟩ :=
    exists_smooth_descent_of_tame_quotient Γ R X X' ρ π t.G s τ hQ hfin hqp hsemi.smooth hw htame hfib
  obtain ⟨_, _, a', hgp, ha⟩ := quotient_descend_grpObj Γ (𝓞 E) X X' ρ π t.G G' φ τ t.act hQ hpb inferInstance
    fun g => ⟨hinv g, hcart g, hact g⟩
  have hsemi' := (SemiAbelianDescent.main X X' π t.G G' φ inferInstance hsurj hgp hsm hsemi).1
  obtain ⟨u, hu₁, hu₂, hu₃⟩ := RigidLinearisation.exists_linearisation Γ X t.G (eSec t.G) ρ τ t.PP.L hsec hgi
    (eq_one_of_appLE_section_eq_one X t.G (eSec t.G) hsec hsemi.smooth hgi hga) (fun g => ⟨hw g, he g⟩) hfib
    t.PP.isLB ⟨t.PP.rig, t.PP.rigGen⟩ hL
  have hQ' := (quotient_flat_baseChange Γ X X' _ _ ρ π φ t.G.hom G'.hom hQ hpb inferInstance).2 τ
    fun g => ⟨hinv g, hw g⟩
  obtain ⟨L', hL', hiso⟩ := LinDescent.exists_descent_of_tame Γ _ _ τ φ t.PP.L hQ' (fun k _ _ y => by
    convert htame k (y ≫ t.G.hom) using 2
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g =>
      fixes_iff_fixes_image t.G.hom _ _ y (hw g) (hfib k _ g))) t.PP.isLB u hu₁ hu₂ hu₃
  obtain ⟨t', ν, e, hν⟩ := T.exists_semiAbelianTriple_of_finiteQuotient E H Γ X X' ρ π t G' a' φ L' hQ hga hsemi' hgp ha hL' hiso
  have hinv' (g : Γ) : (τ g).hom ≫ ν.φ = ν.φ := by
    rw [← cancel_mono e.hom.left, Category.assoc, hν, hinv]
  refine ⟨t', ν, hinv', fun ⟨h₁, h₂, _⟩ hP => ⟨?_, ?_, ?_⟩⟩
  · exact (SemiAbelianDescent.main X X' π t.G t'.G ν.φ inferInstance hsurj ν.cart t'.semi.smooth hsemi).2 h₁
  · exact splitFibres_descend_of_tame_quotient Γ X X' ρ π t.G t'.G ν.φ hQ htame ν.cart h₂
  · obtain ⟨w, hw', -⟩ := ν.lin
    have := t'.semi.smooth
    exact exists_secOn_nonvanishing_of_tame_quotient Γ X X' ρ π t.G t'.G ν.φ τ t.PP.L t'.PP.L hQ ν.cart.1
      inferInstance (fun g => ⟨hinv' g, hw g⟩) htame hfib t.PP.isLB t'.PP.isLB ⟨w, hw'⟩ hP

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFrameOfPreconnected
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ThetaFamily

theorem thetaChar_family {g m : ℕ} {B : Set (Fin m → ℂ)} {p q : Fin g → (Fin m → ℂ) → (Fin g → ℂ)}
    {h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ} (hp : ∀ k, DifferentiableOn ℂ (p k) B)
    (hq : ∀ k, DifferentiableOn ℂ (q k) B)
    (hh : ∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k, (h b).mulVec (p k b) = Pi.single k 1 ∧
      (h b).mulVec (q k b) = (τ b).mulVec (Pi.single k 1))
    {c₁ c₂ : Fin g → ℂ} (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) :
    DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => thetaChar (τ bz.1) c₁ c₂ ((h bz.1).mulVec bz.2))
      (B ×ˢ Set.univ) ∧ ∀ b ∈ B, ∀ z, ∃ᶠ w in nhds z, thetaChar (τ b) c₁ c₂ ((h b).mulVec w) ≠ 0 := by
  have re : ∀ {c : Fin g → ℂ}, (∀ k, c k = 0 ∨ c k = 1 / 2) → ∃ a : Fin g → ℝ, c = fun i => (a i : ℂ) := fun {c} hc =>
    ⟨fun i => (c i).re, funext fun i => by rcases hc i with e | e <;> simp [e]⟩
  obtain ⟨a₁, rfl⟩ := re h₁
  obtain ⟨a₂, rfl⟩ := re h₂
  have hinv : ∀ b ∈ B, h b * Matrix.of (fun i k => p k b i) = 1 := fun b hb => by
    ext i k
    have := congrFun ((hh b hb).2 k).1 i
    rw [Matrix.one_apply, ← Pi.single_apply k (1 : ℂ) i, ← this]
    rfl
  have dh : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) B :=
    differentiableOn_left_inverse (fun i k => differentiableOn_pi.1 (hp k) i) hinv
  have dτ : ∀ i k, DifferentiableOn ℂ (fun b => τ b i k) B := fun i k => by
    refine (DifferentiableOn.fun_sum (u := Finset.univ) fun j _ =>
      (dh i j).mul (differentiableOn_pi.1 (hq k) j)).congr fun b hb => ?_
    have := congrFun ((hh b hb).2 k).2 i
    rw [Matrix.mulVec_single_one] at this
    exact this.symm
  have fst : ∀ {f : (Fin m → ℂ) → ℂ}, DifferentiableOn ℂ f B →
      DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => f bz.1) (B ×ˢ Set.univ) := fun hf =>
    hf.comp differentiableOn_fst fun _ h => h.1
  refine ⟨CanTh.differentiableOn_thetaChar (T := fun bz : (Fin m → ℂ) × (Fin g → ℂ) => τ bz.1)
    (Z := fun bz => (h bz.1).mulVec bz.2) (fun i k => fst (dτ i k)) (differentiableOn_pi.2 fun i => ?_)
    (fun w hw => CanTh.mem_thetaDomain (hh _ hw.1).1) a₁ a₂, fun b hb => ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact DifferentiableOn.fun_sum fun j _ => (fst (dh i j)).mul (by fun_prop)
  · have dl : Differentiable ℂ (fun w : Fin g → ℂ => (h b).mulVec w) :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (h b))).differentiable
    refine frequently_ne_zero_of_entire
      (θ := fun w => thetaChar (τ b) (fun i => (a₁ i : ℂ)) (fun i => (a₂ i : ℂ)) ((h b).mulVec w))
      ((CanTh.differentiable_thetaChar (CanTh.mem_thetaDomain (hh b hb).1) a₁ a₂).comp dl) fun h0 => ?_
    refine thetaChar_ne_zero (hh b hb).1 a₁ a₂ (funext fun w => ?_)
    have := congrFun h0 ((Matrix.of (fun i k => p k b i)).mulVec w)
    rwa [Matrix.mulVec_mulVec, hinv b hb, Matrix.one_mulVec] at this

theorem exists_thetaFrame_of_preconnected : Out.Laws → (∀ (k : Type) [Field k] (X : Scheme.{0}) (s
    : X ⟶ Sp k), Smooth s → IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B
    : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p
    + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
    : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B
    : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶
    Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ Xo.univ.t.G)) (bas : (Fin g ⊕ Fin g →
    ℤ) ≃ₗ[ℤ] D'.La) (sgn : ℤˣ) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ b ∈ B, ((y b) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧
    Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y
    b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P
    b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e
    b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ •
    (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → (∀ a b, D'.EF (bas
    a) (bas b) = sgn * omegaStd a b) → (∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k, (h
    b).mulVec (P b (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ (h b).mulVec (P b (bas (Pi.single
    (.inr k) 1))) = (τ b).mulVec (Pi.single k 1)) → ∀ b₀ ∈ B, ∃! cc : (Fin g → ℂ) × (Fin g →
    ℂ), ∃ c₁ c₂, cc = (c₁,
    c₂) ∧ (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ IsThetaFrame Xo.univ.t.PP {b₀} y (fun b z => (e
    b z).left) (fun b z => thetaChar (τ b) c₁ c₂ ((h b).mulVec z))) → (∀ (X
    : Scheme.{0}) [IsLocallyNoetherian X] (P : Out.PolAV X) (x : X), ∃ (V : X.Opens) (θ
    : ∀ i, Γ(P.A.left, P.A.hom ⁻¹ᵁ V ⊓ P.L.U i)), x ∈ V ∧ θ ∈ secOn P.L (P.A.hom ⁻¹ᵁ
    V) ∧ (∀ y ∈ V, ∃ (a : P.A.left) (i : P.L.ι), P.A.hom a = y ∧ a ∈ P.A.left.basicOpen (θ
    i))) → (∀ (V V' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ
    V] [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V'] (W : Set (V × V')) (f θ F
    : V × V' → ℂ), IsOpen W → DifferentiableOn ℂ f W → DifferentiableOn ℂ θ W → (∀ w ∈ W, F w * θ w = f w) → (∀ b, DifferentiableOn ℂ (fun z => F (b,
    z)) {z | (b, z) ∈ W}) → (∀ w ∈ W, ∃ᶠ z in nhds w.2, θ (w.1,
    z) ≠ 0) → DifferentiableOn ℂ F W) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
    : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty
    : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D'
    : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+
    (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶
    Xo.univ.t.G)) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La) (sgn : ℤˣ) (h τ : (Fin m →
    ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ b ∈ B, ((y b) ≫ Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧
    ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ
    (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b)
    z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ
    ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧
    (∀ z, (e b) z = 1 ↔ z ∈ ((P b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a
    : E) * z k) = (e b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ •
    (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → (∀ a b, D'.EF (bas
    a) (bas b) = sgn * omegaStd a b) → (∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k, (h
    b).mulVec (P b (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ (h b).mulVec (P b (bas (Pi.single
    (.inr k) 1))) = (τ b).mulVec (Pi.single k
    1)) → IsOpen B → IsPreconnected B → IsHolPeriods D' ty B P → IsHolTo B y → IsHolTo (B ×ˢ
    Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1
    bz.2).left) → ∃ c₁ c₂ : Fin g → ℂ, (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ IsThetaFrame Xo.univ.t.PP B y (fun b z => (e
    b z).left) (fun b z => thetaChar (τ b) c₁ c₂ ((h b).mulVec z)) := by
  intro laws hsm hobj hpt hsec _ E _ _ _ H D l Xo σ g ty h1 h2 h3 D' t m B P y e bas sgn h τ hU hbas hh _ hc hP hy hol
  have pt := hpt E H D l Xo σ g ty h1 h2 h3 D' t m B P y e bas sgn h τ hU hbas hh
  have th := fun (c₁ c₂ : Fin g → ℂ) h₁ h₂ => thetaChar_family (c₁ := c₁) (c₂ := c₂)
    (p := fun k b => P b (bas (Pi.single (.inl k) 1))) (q := fun k b => P b (bas (Pi.single (.inr k) 1)))
    (fun k => hP.2 _) (fun k => hP.2 _) hh h₁ h₂
  have he : ∀ b ∈ B, ∀ z, (e b z).left ≫ Xo.univ.t.G.hom = y b := fun b _ z => Over.w (e b z)
  have he0 : ∀ b ∈ B, (e b 0).left = y b ≫ eSec Xo.univ.t.G := fun b hb => by
    rw [((hU b hb).2.2.2.1 0).2 (zero_mem _)]
    rfl
  have := Xo.smooth
  have := (hsm _ _ Xo.s (SmoothOfRelativeDimension.smooth D.dim Xo.s)).2.2
  obtain ⟨o₁, o₂, o₃, o₄⟩ := hobj E H D l _ _ _ _ Xo.univ
  have sec : ∀ b₀ ∈ B, ∃ (V : Xo.X.Opens) (θ₀ : ∀ j, Γ(Xo.univ.t.G.left, Xo.univ.t.G.hom ⁻¹ᵁ V ⊓ Xo.univ.t.PP.L.U j)),
      ⊤ ≤ y b₀ ⁻¹ᵁ V ∧ ∀ b ∈ B, ⊤ ≤ y b ⁻¹ᵁ V → SpansFibre Xo.univ.t.PP (y b) V θ₀ := fun b₀ _ => by
    obtain ⟨V, θ₀, m₀, s₀, n₀⟩ := hsec Xo.X
      { A := Xo.univ.t.G, isAb := o₁, g := _, smoothDim := o₂, L := Xo.univ.t.PP.L, isLB := Xo.univ.t.PP.isLB
        rigid := o₃, sym := o₄, ample := Xo.univ.ample, ktriv := Xo.univ.ktriv } (y b₀ (default : PrimeSpectrum ℂ))
    exact ⟨V, θ₀, (top_le_preimage_iff_mem _ _).2 m₀, fun b _ hb =>
      exists_ratio_fibre laws.globalSectionsRank Xo.univ (y b) V θ₀ s₀ n₀ hb⟩
  choose! c hc₁ hc₂ using pt
  let C₀ : Set (Fin g → ℂ) := Set.pi Set.univ fun _ => {0, 1 / 2}
  have fin : (C₀ ×ˢ C₀).Finite := (Set.Finite.pi fun _ => Set.toFinite _).prod (Set.Finite.pi fun _ => Set.toFinite _)
  have hc₃ : ∀ b ∈ B, (∀ k, (c b).1 k = 0 ∨ (c b).1 k = 1 / 2) ∧ (∀ k, (c b).2 k = 0 ∨ (c b).2 k = 1 / 2) ∧
      ∃ fr, IsFibreFrame Xo.univ.t.PP (y b) (fun z => (e b z).left)
        (fun z => thetaChar (τ b) (c b).1 (c b).2 ((h b).mulVec z)) fr := fun b hb => by
    obtain ⟨c₁, c₂, e₀, r₁, r₂, r₃⟩ := hc₁ b hb
    have r := isThetaFrame_singleton_iff.1 r₃
    rw [e₀]
    exact ⟨r₁, r₂, r⟩
  have const := eq_of_finite_of_closed_fibres hc fin c
    (fun b hb => ⟨fun k _ => (hc₃ b hb).1 k, fun k _ => (hc₃ b hb).2.1 k⟩) (fun k hk b hb hcl => by
      have k₁ := fun i => hk.1 i trivial
      have k₂ := fun i => hk.2 i trivial
      obtain ⟨V, θ₀, hV₀, hV⟩ := sec b hb
      obtain ⟨fr', h'⟩ := (hc₃ b hb).2.2
      have r := exists_fibreFrame_of_mem_closure (e := fun b z => (e b z).left)
        (θ := fun b z => thetaChar (τ b) k.1 k.2 ((h b).mulVec z)) he hol (th _ _ k₁ k₂).1 (th _ _ k₁ k₂).2 hb hV₀ hV
        (T := {b' ∈ B | c b' = k}) (fun b' hb' => by have r := (hc₃ b' hb'.1).2.2; rw [hb'.2] at r; exact r) hcl
        ((th _ _ (hc₃ b hb).1 (hc₃ b hb).2.1).2 b hb) h'
      exact (hc₂ b hb k ⟨k.1, k.2, rfl, k₁, k₂, (isThetaFrame_singleton_iff (y := y) (e := fun b z => (e b z).left)
        (θ := fun b z => thetaChar (τ b) k.1 k.2 ((h b).mulVec z))).2 r⟩).symm)
  obtain ⟨k, k₁, k₂, hk⟩ : ∃ k : (Fin g → ℂ) × (Fin g → ℂ), (∀ i, k.1 i = 0 ∨ k.1 i = 1 / 2) ∧
      (∀ i, k.2 i = 0 ∨ k.2 i = 1 / 2) ∧ ∀ b ∈ B, c b = k := by
    rcases B.eq_empty_or_nonempty with h0 | ⟨b₀, hb₀⟩
    · exact ⟨0, fun _ => Or.inl rfl, fun _ => Or.inl rfl, fun b hb => absurd (h0 ▸ hb) (Set.notMem_empty b)⟩
    · exact ⟨c b₀, (hc₃ b₀ hb₀).1, (hc₃ b₀ hb₀).2.1, fun b hb => const b hb b₀ hb₀⟩
  exact ⟨k.1, k.2, k₁, k₂, isThetaFrame_of_fibreFrames (e := fun b z => (e b z).left)
    (θ := fun b z => thetaChar (τ b) k.1 k.2 ((h b).mulVec z)) he he0 hy hol (th _ _ k₁ k₂).1 (th _ _ k₁ k₂).2 sec
    fun b hb => by have r := (hc₃ b hb).2.2; rw [hk b hb] at r; exact r⟩

end GlobalTheory.ThetaFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaObjPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left}

theorem pushHom_injective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Injective (pushHom h T) :=
  fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) (by rw [Over.w, Over.w]))

theorem pushHom_surjective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Surjective (pushHom h T) :=
  fun y => ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem map_linComb {T : Over S} {T' : Over S'} (ρ : (T' ⟶ A') →* (T ⟶ A)) {n : ℕ} (y : Fin n → (T' ⟶ A'))
    (a : Fin n → ℕ) : ρ (Out.linComb y a) = Out.linComb (fun i => ρ (y i)) a := by
  unfold Out.linComb
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  exact map_pow ρ _ _

def toBase (f : S' ⟶ S) : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S := Over.homMk f (by simp)

theorem exists_sec (h : IsGrpPullback A' A f φ) (x : Out.baseOver S ⟶ A) :
    ∃ x' : Out.baseOver S' ⟶ A', pushHom h _ x' = toBase f ≫ x :=
  pushHom_surjective h _ _

end GlobalTheory.ThetaObjPull

namespace GlobalTheory

open ThetaObjPull PolBaseChange

theorem tObj_pull : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' : Scheme.{0})
    (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s), f ≫ s = s' →
    ∃ t' : TObj g k J b s', TMap t' t f := by
  intro o _ g k J b S S' s s' f t hs
  subst hs
  have h := isGrpPullback_pullback t.A f
  have hL' := pull_isLB t.isLB (pullback.fst t.A.hom f)
  have hiso := lbIso_refl hL'
  obtain ⟨hab, hamp, hk⟩ := pol_pull _ _ _ _ _ _ _ _ t.isLB hL' t.ab h hiso
  choose pt hpt using fun i => exists_sec h (t.pt i)
  have hpt' : ∀ i, (pt i).left ≫ pullback.fst t.A.hom f = f ≫ (t.pt i).left := fun i =>
    congrArg (fun z => z.left) (hpt i)
  have := t.hom
  have := t.ab.comm
  refine ⟨{ A := (Over.pullback f).obj t.A
            ab := hab
            dim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 t.dim
            L := t.L.pull (pullback.fst t.A.hom f)
            isLB := hL'
            rigid := rigidified_pull h t.rigid
            sym := sym_pull h t.sym
            ample := hamp t.ample
            ktriv := hk t.ktriv
            pt := pt
            torsion := fun i => pushHom_injective h _ ?_
            bij := fun K _ _ x y hy => ?_
            pairing := fun i j => ?_
            act := fun j => (Over.pullback f).map (t.act j)
            hom := fun j => inferInstance }, pullback.fst t.A.hom f, h, hiso, hpt', fun j => pullback.lift_fst _ _ _⟩
  · rw [map_pow, map_one, hpt]
    exact (map_pow (preHom (toBase f)) _ _).symm.trans (by rw [t.torsion, map_one])
  · have key : ∀ c : Ix g k, pushHom h (Over.mk x) (Out.linComb (fun i =>
        (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S') ≫ pt i) (fun i => (c i).val)) =
        Out.linComb (fun i => (Over.homMk (x ≫ f) (by simp) : Over.mk (x ≫ f) ⟶ Out.baseOver S) ≫ t.pt i)
          (fun i => (c i).val) := fun c => by
      rw [map_linComb]
      congr 1
      funext i
      apply Over.OverMorphism.ext
      show (x ≫ (pt i).left) ≫ _ = (x ≫ f) ≫ (t.pt i).left
      rw [Category.assoc, hpt', Category.assoc]
    have hy' : pushHom h (Over.mk x) y ^ k = 1 := by rw [← map_pow, hy, map_one]
    obtain ⟨c, hc, hu⟩ := t.bij K (x ≫ f) (pushHom h (Over.mk x) y) hy'
    exact ⟨c, pushHom_injective h _ ((key c).trans hc), fun c' hc' => hu c' ((key c').symm.trans (congrArg _ hc'))⟩
  · refine (weilIs_grpPullback_of_comm _ _ _ _ f _ _ _ t.isLB hL' h hiso (Out.baseOver S') k (pt i) (pt j)
      (toBase f ≫ t.pt i) (toBase f ≫ t.pt j) _ (hpt' i).symm (hpt' j).symm).2 ?_
    have w := CommPairing.weilIs_pull globalFns_holds t.ab t.isLB (toBase f) (t.pairing i j)
    rw [map_zpow] at w
    have e : Units.map (toBase f).left.appTop.hom.toMonoidHom (unitS s b.ζ) = unitS (f ≫ s) b.ζ := by
      apply Units.ext
      show f.appTop.hom (s.appTop.hom _) = (f ≫ s).appTop.hom _
      rw [Scheme.Hom.comp_appTop]
      rfl
    exact e ▸ w

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankSectionsPullbackMulByNTwistsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionsHaveFiniteDimension_lbDiv_linComb : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (k r : ℕ), M.IsLB → (k : K) ≠ 0 → (∀ y : 𝟙_ (Over (Sp K)) ⟶ P.A, y ^ k = 1 → SectionsHaveFiniteDimension P.A.hom (LB.div M (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, ((toUnit P.A ≫ y) * 𝟙 P.A).left] ![1, -1])) r) → SectionsHaveFiniteDimension P.A.hom (M.pull (Out.mulA P.A k).left) (k ^ (2 * P.g) * r) := by
  first | exact @GlobalTheory.TwistSplit.finrank_sections_pullback_mulByN_twists | exact GlobalTheory.TwistSplit.finrank_sections_pullback_mulByN_twists | (intros; apply GlobalTheory.TwistSplit.finrank_sections_pullback_mulByN_twists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasThetaConstants_ring_baseChange : Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), t.HasTh x v → t.HasTh (spMap φ ≫ x) (fun a => φ (v a)) := by
  first | exact @GlobalTheory.hasTh_baseChange | exact GlobalTheory.hasTh_baseChange | (intros; apply GlobalTheory.hasTh_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelStructureDescendsFieldExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pelStructure_descends_field_extension : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g k : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (β₀ : o →+* K₀) (s : Sp K ⟶ Sp o) (t₀ : TObj g k J b (spMap β₀)) (t : TObj g k J b s) (τ : SAB H (Sp K)), Subring.closure (Set.range a) = ⊤ → s = spMap i ≫ spMap β₀ → TMap t t₀ (spMap i) → IsPEL D a bas ρ t τ → ∃ τ₀ : SAB H (Sp K₀), IsPEL D a bas ρ t₀ τ₀ := by
  first | exact @GlobalTheory.PELDesc.isPEL_descends | exact GlobalTheory.PELDesc.isPEL_descends | (intros; apply GlobalTheory.PELDesc.isPEL_descends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAbelianSchemeConstOverDualNumbersStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.thetaLevelAbelianScheme_const_over_dualNumbers : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (w w' : J) (K : Type) [Field K] (s : Sp (DualNumber K) ⟶ Sp o) (s₀ : Sp K ⟶ Sp o) (t : TObj g k J b s) (t₀ : TObj g k J b s₀) (io : t₀.A.left ⟶ t.A.left) (ψ₀ : t.A.left ⟶ t₀.A.left), t.Prim w w' → IsGrpPullback t₀.A t.A (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) io → LBIso t₀.L (t.L.pull io) → (∀ i, (t₀.pt i).left ≫ io = spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (t.pt i).left) → (∀ j, (t₀.act j).left ≫ io = io ≫ (t.act j).left) → IsGrpPullback t.A t₀.A (spMap (algebraMap K (DualNumber K))) ψ₀ → io ≫ ψ₀ = 𝟙 _ → TMap t t₀ (spMap (algebraMap K (DualNumber K))) := by
  first | exact @GlobalTheory.ConstTheta.tMap_of_const | exact GlobalTheory.ConstTheta.tMap_of_const | (intros; apply GlobalTheory.ConstTheta.tMap_of_const <;> assumption)
end

