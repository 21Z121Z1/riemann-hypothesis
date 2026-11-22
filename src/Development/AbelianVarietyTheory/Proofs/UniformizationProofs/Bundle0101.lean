import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0091
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusQuotientCardTorsion
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU
namespace TorsionCount

theorem card_torsion_eq_mul {A B : Type} [CommGroup A] [CommGroup B] (f : A →* B) (N : ℕ)
    (h : ∀ b : B, b ^ N = 1 → ∃ a : A, a ^ N = 1 ∧ f a = b) :
    Nat.card {a : A // a ^ N = 1} = Nat.card {a : A // a ^ N = 1 ∧ f a = 1} * Nat.card {b : B // b ^ N = 1} := by
  choose s hs hs' using h
  rw [← Nat.card_prod]
  have hf : ∀ a : A, a ^ N = 1 → f a ^ N = 1 := fun a ha => by rw [← map_pow, ha, map_one]
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : {a : A // a ^ N = 1 ∧ f a = 1} × {b : B // b ^ N = 1} =>
      (⟨x.1.1 * s x.2.1 x.2.2, by rw [mul_pow, x.1.2.1, hs, _root_.one_mul]⟩ : {a : A // a ^ N = 1})) ⟨?_, ?_⟩).symm
  · rintro ⟨⟨a, ha⟩, b, hb⟩ ⟨⟨a', ha'⟩, b', hb'⟩ e
    have e₁ : a * s b hb = a' * s b' hb' := congrArg Subtype.val e
    have e₂ := congrArg f e₁
    rw [map_mul, map_mul, hs', hs', ha.2, ha'.2, _root_.one_mul, _root_.one_mul] at e₂
    subst e₂
    have e₃ := mul_right_cancel e₁
    subst e₃
    rfl
  · rintro ⟨a, ha⟩
    refine ⟨(⟨a * (s (f a) (hf a ha))⁻¹, ?_, ?_⟩, ⟨f a, hf a ha⟩), Subtype.ext (inv_mul_cancel_right _ _)⟩
    · rw [mul_pow, inv_pow, ha, hs, inv_one, _root_.one_mul]
    · rw [map_mul, map_inv, hs', mul_inv_cancel]

theorem card_hom_torsion {X U : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [CommGroup U] (N : ℕ) :
    Nat.card {φ : Multiplicative X →* U // φ ^ N = 1} = Nat.card {u : U // u ^ N = 1} ^ Module.finrank ℤ X := by
  let e := Module.finBasis ℤ X
  have key : Function.Bijective (fun (φ : {φ : Multiplicative X →* U // φ ^ N = 1}) (k : Fin (Module.finrank ℤ X)) =>
      (⟨φ.1 (Multiplicative.ofAdd (e k)), DFunLike.congr_fun φ.2 _⟩ : {u : U // u ^ N = 1})) := by
    have ext : ∀ φ ψ : Multiplicative X →* U,
        (∀ k, φ (Multiplicative.ofAdd (e k)) = ψ (Multiplicative.ofAdd (e k))) → φ = ψ := fun φ ψ h => by
      have : (MonoidHom.toAdditiveRight φ).toIntLinearMap = (MonoidHom.toAdditiveRight ψ).toIntLinearMap :=
        e.ext fun k => congrArg Additive.ofMul (h k)
      exact MonoidHom.ext fun χ => congrArg Additive.toMul (LinearMap.congr_fun this (Multiplicative.toAdd χ))
    constructor
    · intro φ ψ h
      exact Subtype.ext (ext _ _ fun k => congrArg Subtype.val (congrFun h k))
    · intro v
      let l : X →ₗ[ℤ] Additive U := e.constr ℤ fun k => Additive.ofMul (v k).1
      have hl : ∀ k, AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom (Multiplicative.ofAdd (e k)) = (v k).1 :=
        fun k => congrArg Additive.toMul (e.constr_basis ℤ _ k)
      refine ⟨⟨AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom, ext _ _ fun k => ?_⟩,
        funext fun k => Subtype.ext (hl k)⟩
      rw [MonoidHom.pow_apply, hl, (v k).2, MonoidHom.one_apply]
  rw [Nat.card_congr (Equiv.ofBijective _ key), Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]

theorem card_units_torsion (K : Type) [Field K] [IsAlgClosed K] {N : ℕ} (hN : (N : K) ≠ 0) :
    Nat.card {u : Kˣ // u ^ N = 1} = N := by
  have : NeZero (N : K) := ⟨hN⟩
  have : NeZero N := NeZero.of_neZero_natCast K
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity K N

theorem card_torsion_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) (N : ℕ) :
    Nat.card {a : A // a ^ N = 1} = Nat.card {b : B // b ^ N = 1} :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun a => by
    rw [← e.map_eq_one_iff, map_pow]; rfl)

end TorsionCount

open TorsionCount in

theorem torusQuotient_card_torsion :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G]
      [IsCommMonObj G] (Q : TQ G X) (K : Type) [Field K] [IsAlgClosed K] (p : Spec (CommRingCat.of K) ⟶ S) (N : ℕ),
      (N : K) ≠ 0 → Nat.card {x : Over.mk p ⟶ G // x ^ N = 1 ∧ x ≫ Q.q = 1} = N ^ Module.finrank ℤ X ∧
        Nat.card {x : Over.mk p ⟶ G // x ^ N = 1} =
          N ^ Module.finrank ℤ X * Nat.card {b : Over.mk p ⟶ Q.B // b ^ N = 1} := by
  intro S X _ _ _ G _ _ Q K _ _ p N hN
  have := Q.q_hom
  have := Q.i_hom
  have hN' : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; exact hN Nat.cast_zero)
  let e : Kˣ ≃* Γ(Spec (CommRingCat.of K), ⊤)ˣ :=
    Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.toMulEquiv
  have inj : ∀ t t' : Over.mk p ⟶ splitTorus S X, t ≫ Q.i = t' ≫ Q.i → t = t' := fun t t' h =>
    Q.isKernel.hom_ext h (toUnit_unique _ _)
  have h₃ : ∀ t : Over.mk p ⟶ splitTorus S X, (t ≫ Q.i) ≫ Q.q = 1 := fun t => by
    rw [Category.assoc, Q.isKernel.w, ← Category.assoc, Hom.one_def, toUnit_unique (t ≫ toUnit _) (toUnit _)]
  have key : Function.Bijective (fun t : {t : Over.mk p ⟶ splitTorus S X // t ^ N = 1} =>
      (⟨t.1 ≫ Q.i, by rw [← MonObj.pow_comp, t.2, MonObj.one_comp], h₃ _⟩ :
        {x : Over.mk p ⟶ G // x ^ N = 1 ∧ x ≫ Q.q = 1})) := by
    refine ⟨fun t t' h => Subtype.ext (inj _ _ (congrArg Subtype.val h)), ?_⟩
    rintro ⟨x, hx, hq⟩
    have h₁ : x ≫ Q.q = toUnit _ ≫ η[Q.B] := hq.trans Hom.one_def
    refine ⟨⟨Q.isKernel.lift _ _ h₁, inj _ _ ?_⟩, Subtype.ext (Q.isKernel.lift_fst _ _ _)⟩
    rw [MonObj.pow_comp, IsPullback.lift_fst, hx, MonObj.one_comp]
  have c₁ : Nat.card {x : Over.mk p ⟶ G // x ^ N = 1 ∧ x ≫ Q.q = 1} = N ^ Module.finrank ℤ X := by
    rw [← Nat.card_congr (Equiv.ofBijective _ key), card_torsion_congr (splitTorusPointsEquiv S X (Over.mk p)) N,
      card_hom_torsion]
    exact congrArg (· ^ _) ((card_torsion_congr e N).symm.trans (card_units_torsion K hN))
  refine ⟨c₁, ?_⟩
  rw [← c₁]
  refine card_torsion_eq_mul (MonoidHom.mk' (fun x : Over.mk p ⟶ G => x ≫ Q.q) fun x y => MonObj.mul_comp _ _ _) N
    ((torusQuotient_points_lift S X G Q K p).2 N fun a => ?_)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (a : K) hN'
  have h0 : r ≠ 0 := by
    rintro rfl
    exact a.ne_zero (hr.symm.trans (zero_pow hN'.ne'))
  exact ⟨Units.mk0 r h0, Units.ext (by simpa using hr)⟩

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTermsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.valuations_torusPoints_frames_familyTerms : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ g : GtPtF D.toPre F, (∃! l : D.toPre.X →+ ℚ, GtV hϖ hv g l) ∧ (∀ (k : ℕ) (w : Frm D.toPre F k g.b), w.IsGen → ∃! r, GenV hϖ hv w r) ∧ (∀ (k : ℕ) (w : Frm D.toPre F k g.b), FrmOne w → g.b = 1 → GenV hϖ hv w 0) ∧ (∀ (g' g'' : GtPtF D.toPre F) l l', g.IsAdd g' g'' → GtV hϖ hv g l → GtV hϖ hv g' l' → GtV hϖ hv g'' (l + l')) ∧ (∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, GtV hϖ hv p.g fun χ => (QForm.bOf D.toPre Q p.y χ : ℚ) / k) ∧ (∀ y, GtPtF.IsIota y g → GtV hϖ hv g fun χ => (QForm.bOf D.toPre Q y χ : ℚ)) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (w : Frm D.toPre F k g.b) (s : Fam D.toPre F k), w.IsGen → NullV v (coef s g w) ∧ ∀ l ω r, GtV hϖ hv g l → GenV hϖ hv w ω → NuGe D Q F v k s r → ∀ χ, ((r + (Q χ : ℚ) / k + l χ + ω : ℚ) : WithTop ℚ) ≤ v (coef s g w χ) := by
  first | exact @GlobalTheory.UT.CoefVal.main | exact GlobalTheory.UT.CoefVal.main | (intros; apply GlobalTheory.UT.CoefVal.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

open TopologicalSpace GlobalTheory.AmpleLocal

theorem gs_cst {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (D : X.Opens) (c : R)
    (z : X) (hz : z ∈ D) : gs (𝟙 X) z D (AbLaw.cst f D c) = gs (𝟙 X) z ⊤ (AbLaw.cst f ⊤ c) := by
  rw [← rs_cst f (le_top : D ≤ ⊤) c]
  exact gs_res (𝟙 X) z le_top hz _

theorem veryAmpleBy_pw : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X)
    (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, 1 ≤ d →
    ∃ (n' : ℕ) (s' : Fin (n' + 1) → LB.Sec (pw H d)), VeryAmpleBy f (pw H d) s' := by
  intro R _ X f H n s hH ⟨cov, hs⟩ d hd
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  choose aff r hr surj using hs
  choose c hc using fun z : X => exists_chart hH z
  let G : H.ι → Fn X := fun i z => (gm (𝟙 X) z _ (H.g i (c z))).val
  let φ : R → Fn X := fun a z => gs (𝟙 X) z ⊤ (AbLaw.cst f ⊤ a)
  have hU : ∀ z, ∃ i, z ∈ H.U i := fun z => ⟨c z, hc z⟩
  have hG : ∀ i z, IsUnit (G i z) := fun _ _ => Units.isUnit _
  let σ : Fin (n + 1) → Fn X := fun i => sv c (s i)
  have hσ : ∀ i, Sc H.U G ⊤ 1 (σ i) := fun i =>
    sc_sv (P := H) (κ := id) (fun _ => le_rfl) hc (fun _ _ _ => (pow_one _).symm) (s i)
  have gen : ∀ i, Gen (nonzeroLocus (s i)) (Set.range φ ∪ Set.range fun m => σ m * AmpleLocal.inv (σ i)) := fun i =>
    (gen_iff _ (r i) _ _ (fun a z hz => gs_cst f _ a z hz)
      (fun m => (ratio_iff hc (s i) (s m) (r i m)).1 (hr i m))).2 (surj i)
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_pos (α := Fin (n + 1) × Fin (n + 1))).ne'
  let ε := Fintype.equivFinOfCardEq hM
  let τ : Fin (M + 1) → Fn X := fun m => σ (ε.symm m).2 * σ (ε.symm m).1 ^ e
  have hτ : ∀ m, Sc H.U G ⊤ (1 * (e + 1)) (τ m) := fun m => by
    rw [mul_add, _root_.mul_one, add_comm]
    exact (hσ _).mul ((hσ _).pow _)
  have hγ : ∀ y, y ∈ (pw H ((e + 1 : ℕ) : ℤ)).U (c y) := hc
  choose t ht using fun m => exists_sv (P := pw H ((e + 1 : ℕ) : ℤ)) (κ := id) (N := 1 * (e + 1)) (G := G)
    (fun _ => le_rfl) hc (fun i y _ => by
      show (gm (𝟙 X) y _ (H.g i (c y) ^ ((e + 1 : ℕ) : ℤ))).val = _
      rw [zpow_natCast, map_pow, Units.val_pow_eq_pow_val, _root_.one_mul]) (isLB_pw hH _) (hτ m)
  have loc : ∀ m, IsLoc (nonzeroLocus (t m)) ⊤ (τ m) := fun m => ht m ▸ loc_sv hγ (t m)
  have main := fun m => extra_section hU hG hσ (fun i => loc_sv hc (s i))
    (fun z _ => Opens.mem_iSup.1 (cov.ge trivial)) aff (S₀ := Set.range φ)
    (by rintro _ ⟨a, rfl⟩; exact mem_reg_iff.2 ⟨_, fun _ _ => rfl⟩) gen (hτ m) (loc m)
  refine ⟨M, t, top_le_iff.1 fun z _ => ?_, fun i => ⟨(main i).1, ?_⟩⟩
  · obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (cov.ge (Set.mem_univ z))
    have hu : IsUnit (σ j z) := (loc_sv hc (s j)).unit hj
    refine Opens.mem_iSup.2 ⟨ε (j, j), (loc _ z).2 ⟨trivial, ?_⟩⟩
    simp only [τ, Equiv.symm_apply_apply]
    exact hu.mul (hu.pow e)
  · choose ρ hρ using fun m => mem_reg_iff.1 (Sc.ratio hU hG (hτ m) (hτ i) (loc i))
    refine ⟨ρ, fun m => (ratio_iff hγ (t i) (t m) (ρ m)).2 ?_, ?_⟩
    · have e₁ : sv (P := pw H ((e + 1 : ℕ) : ℤ)) c (t i) = τ i := ht i
      have e₂ : sv (P := pw H ((e + 1 : ℕ) : ℤ)) c (t m) = τ m := ht m
      rw [e₁, e₂]
      exact hρ m
    · refine (gen_iff _ ρ φ _ (fun a z hz => gs_cst f _ a z hz) hρ).1 ((main i).2.mono ?_)
      rintro x (hx | ⟨p, rfl⟩)
      · exact ⟨x, Subring.subset_closure (Or.inl hx), fun _ _ => rfl⟩
      · refine ⟨_, Subring.subset_closure (Or.inr ⟨ε p, ?_⟩), fun _ _ => rfl⟩
        simp only [τ, Equiv.symm_apply_apply]

end GlobalTheory.AbLaw
end

