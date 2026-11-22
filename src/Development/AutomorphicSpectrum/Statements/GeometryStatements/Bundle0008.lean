import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0112
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExists
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0064

-- bundled from Development.AutomorphicSpectrum.Statements.GeometryStatements.EqOfSpecializes
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CmpHodgeDiag

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

section Ident

open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

def pullIdIso {X : Scheme.{0}} (L : LB X) : LB.Iso L (L.pull (𝟙 X)) where
  s := fun p => res (X := X) (U := L.U (p.1 PUnit.unit) ⊓ L.U p.2)
    (V := (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2) (fun _ hx => ⟨mem_pull.1 hx.1, hx.2⟩) (L.g (p.1 PUnit.unit) p.2)

theorem gw_pullIdIso {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (y : Y) (j k : L.ι) (hj : f y ∈ L.U j)
    (hk : f y ∈ L.U k) : gw (pullIdIso L) f y j k = gm f y (L.U j ⊓ L.U k) (L.g j k) := by
  have hm : f y ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k := ⟨mem_pull.2 hj, hk⟩
  exact gm_res f y _ hm _

theorem pgen_pullIdIso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : PGen (pullIdIso L) := by
  intro Y f y j j' k k' hj hj' hk hk'
  have hj₁ : f y ∈ L.U j := hj
  have hj₂ : f y ∈ L.U j' := hj'
  rw [gw_pullIdIso L f y j k hj₁ hk, gw_pullIdIso L f y j' k' hj₂ hk', Category.comp_id]
  have a := gm_cocycle hL f y hj₁ hk hk'
  have b := gm_cocycle hL f y hj₁ hj₂ hk'
  rw [mul_right_comm, b, ← a, mul_inv_cancel_right]

theorem pmaps_pullIdIso {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : PMaps (pullIdIso L) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  have hp' : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  have hm : r z ∈ LB.wchart L φ p ⊓ LB.wchart L φ q := ⟨Set.mem_iInter.2 hp', Set.mem_iInter.2 hq⟩
  have e := congrArg (gm r z (LB.wchart L φ p ⊓ LB.wchart L φ q)) (ht p q)
  rw [Category.comp_id]
  refine (gm_res r z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  refine (gm_res r z _ hm _).trans ((gm_pull r (φ k) z (L.U (p k) ⊓ L.U (q k)) ⟨hp' k, hq k⟩ _).trans ?_)
  exact (gw_pullIdIso L (r ≫ φ k) z (p k) (q k) (hp' k) (hq k)).symm

def cubeMapId {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] : CubeMap G G where
  F := 𝟙 _
  F3 := 𝟙 _
  e := 𝟙 _
  e_comm := by rw [Category.comp_id, Category.id_comp]
  psum_comm := fun _ => by rw [Category.comp_id, Category.id_comp]

theorem isPullCubical_id {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {L : RigLB G}
    (c : CubicalStr G L) : (cubeMapId G).IsPullCubical c c :=
  (isPullCubical_iff _ _ _).2 ⟨pullIdIso L.L, pgen_pullIdIso L.isLB,
    pmaps_pullIdIso (K := PUnit) (fun _ => eSec G) (fun _ => 1) L.rig L.rigGen,
    pmaps_pullIdIso (thφ G (x3 G)) thε c.t c.isGen⟩

theorem isGrpPullback_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (mul_left_congr (G := G) (Category.comp_id T.hom) x₀ y₀ x y (hx.trans (Category.comp_id _))
    (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm

end Ident

theorem exists_gen {X : Type} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    {U : Set X} (hU : IsOpen U) (hd : Dense U) (y : X) : ∃ g ∈ U, g ⤳ y := by
  obtain ⟨o, ho, hne, hoZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _
      (irreducibleComponent_mem_irreducibleComponents y)
  obtain ⟨z, hzo, hzU⟩ := hd.inter_open_nonempty o ho hne
  obtain ⟨g, hg⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := y))
    (isClosed_irreducibleComponent (x := y))
  exact ⟨g, (hg.specializes (hoZ hzo)).mem_open hU hzU, hg.specializes mem_irreducibleComponent⟩

theorem eq_of_specializes {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ)
    {p : X} (hp : p ⤳ genPt ξ) : p = genPt ξ := by
  obtain ⟨hbij, -⟩ := h
  obtain ⟨q, rfl⟩ : p ∈ Set.range (X.fromSpecStalk (GlobalTheory.CompanionTheory.Ar.genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]
    exact hp
  have hF : IsField (X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ)) :=
    MulEquiv.isField (Field.toIsField Ω) (RingEquiv.ofBijective _ hbij).toMulEquiv
  have hsub : Subsingleton (PrimeSpectrum (X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ))) := by
    letI := hF.toField
    infer_instance
  have hq : q = IsLocalRing.closedPoint (X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ)) :=
    @Subsingleton.elim _ hsub q _
  rw [hq]
  exact Scheme.fromSpecStalk_closedPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
  {Y : Model Xo c β} {Y' : Model Xo c β'} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

def sabMapId {T : Scheme.{0}} (t : SAB H T) : SABMap t t (𝟙 T) where
  cm := cubeMapId t.G
  cart := isGrpPullback_id t.G
  base := rfl
  act := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm
  lin := isPullCubical_id t.G t.cub

end GlobalTheory.CompanionTheory.Ar.CmpHodgeDiag
end
end

-- bundled from Development.AutomorphicSpectrum.Statements.GeometryStatements.NearRecordOfValue
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar.Top

def RootFlatOnHodge : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
    (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (bad : Finset ℕ) (M : RootModel (CMType H) (D.p + D.q))
    (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys)
    (o : RootOrigin Y bad M Fx),
    IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → (∀ r : ℕ, r ∈ bad ↔ r.Prime ∧ (r : ℤ) ∣ 2 * discr E * l.M') →
      o.𝔐.OmVB → ∀ τ, ∃ R : RootFlat M τ, NearRecord (D.p + D.q) bad (hostRd E) (hostLval H) R.ht

namespace OnHodge

section Tower

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {Xo : ∀ l : Level H, Moduli D l} {l : Level H} {c : Coeff l} {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)}

theorem hostRd_eq (E : Type) [Field E] [NumberField E] : hostRd E = rootDiscr E := by
  simp [hostRd, rootDiscr_def]

theorem S_two {T : RootTower (CMType H) (D.p + D.q)} (o : TowerOrigin Y T) : o.S 2 = T.bad := by
  ext r
  rw [o.S_iff, RootTower.InS]
  refine ⟨fun h => h.2.elim (fun h2 => ?_) id, fun h => ⟨((o.bad_iff r).1 h).1, Or.inr h⟩⟩
  obtain rfl : r = 2 := le_antisymm h2 h.1.two_le
  exact T.two_mem

theorem tower (h : RootFlatOnHodge) [IsAbelianGalois ℚ E] (hY : IsGlobal Xo l c Y)
    {T : RootTower (CMType H) (D.p + D.q)} (hT : IsTowerOf Y T) (a : T.Comp) (τ : CMType H) :
    ∃ R : RootFlat (T.M 2 a) τ, NearRecord (D.p + D.q) T.bad (hostRd E) (hostLval H) R.ht := by
  obtain ⟨o, ho⟩ := hT
  have h1 := T.j_pos
  have h2 := T.j_lt
  have h3 := o.j_eq
  rw [← S_two o]
  exact h E H D Xo l c Y (o.S 2) (T.M 2 a) (o.Sys a) (o.Fx a) (o.Or 2 a) hY (by omega) (by omega)
    (fun r => by rw [S_two o]; exact o.bad_iff r) (ho 2 a) τ

end Tower

theorem const_le : Real.eulerMascheroniConstant + Real.log (2 * Real.pi) + 2 * Real.log 2 ≤ 2 * Real.log 7 := by
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  have he : Real.exp (2 / 3) ≤ 1.9496 := by
    have h3 : Real.exp (2 / 3) ^ 3 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    have h1 := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    refine le_of_pow_le_pow_left₀ three_ne_zero (by norm_num) ?_
    rw [h3]; nlinarith
  have h : Real.log (Real.exp (2 / 3) * (2 * Real.pi) * 2 ^ 2) ≤ Real.log (7 ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith [Real.exp_pos (2 / 3)])
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_exp,
    Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

theorem value_bound (p q : ℕ) (lK l L : ℝ) (h7 : Real.log 7 / 2 ≤ lK) (hl : lK ≤ l) :
    |((p : ℝ) - q) / 2 * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - l - L) + q * (2 * lK - l)| +
      ((p + q : ℕ) : ℝ) * Real.log 2 ≤ ((p + q : ℕ) : ℝ) * (3 / 2 * l + |L| / 2) := by
  have hc := const_le
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h4 : 2 * Real.log 2 ≤ Real.log (2 * Real.pi) := by
    have : Real.log (2 ^ 2) ≤ Real.log (2 * Real.pi) :=
      Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_three])
    rw [Real.log_pow] at this
    exact_mod_cast this
  have hL := le_abs_self L
  have hL' := neg_abs_le L
  have hp : (0 : ℝ) ≤ p := p.cast_nonneg
  have hq : (0 : ℝ) ≤ q := q.cast_nonneg
  set c := Real.eulerMascheroniConstant + Real.log (2 * Real.pi) with hcdef
  set b := 3 / 2 * l + |L| / 2 - Real.log 2 with hb
  have a1 : 0 ≤ b - (c - l - L) / 2 := by linarith
  have a2 : 0 ≤ b + (c - l - L) / 2 := by linarith
  have a3 : 0 ≤ b - (-(c - l - L) / 2 + 2 * lK - l) := by linarith
  have a4 : 0 ≤ b + (-(c - l - L) / 2 + 2 * lK - l) := by linarith
  have : |((p : ℝ) - q) / 2 * (c - l - L) + q * (2 * lK - l)| ≤ (p + q) * b :=
    abs_le.2 ⟨by nlinarith [mul_nonneg hp a2, mul_nonneg hq a4], by nlinarith [mul_nonneg hp a1, mul_nonneg hq a3]⟩
  push_cast
  nlinarith

end OnHodge

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

