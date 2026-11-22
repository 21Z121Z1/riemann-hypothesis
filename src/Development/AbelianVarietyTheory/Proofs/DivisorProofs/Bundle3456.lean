import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3439
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkIsIffWeilIsAbelianPart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorOfSymmetricRelat
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3436
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3448

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGradedTateIsoLowerDatum
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat.GradedTate

theorem exists_tateIso_of_perp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw D' : Datum H)
    (Z : Submodule (𝓞 E) Dw.La) (f : perp Dw Z →ₗ[𝓞 E] D'.La) (hf : IsLower Dw D' Z f) (K : Type) [Field K]
    (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (ζ : ℕ → Kˣ)
    (hζ : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) (hζ' : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n)
    (b : ℕ → perp Dw Z → Q) (hact : ∀ c, act c 1 = 1)
    (hcard : ∀ n, 0 < n → Nat.card {y : Q // y ^ n = 1} = n ^ Module.finrank ℤ D'.La)
    (huniq : ∀ n x y c c', e n x y c → e n x y c' → c = c')
    (hone : ∀ n y c, e n 1 y c → c = 1)
    (hadd : ∀ n, 0 < n → ∀ a a', b n (a + a') = b n a * b n a')
    (hlin : ∀ n, 0 < n → ∀ (c : 𝓞 E) a, b n (c • a) = act c (b n a))
    (hpow : ∀ n, 0 < n → ∀ a, b n a ^ n = 1)
    (htow : ∀ n m, 0 < n → 0 < m → ∀ a, b (n * m) a ^ m = b n a)
    (hiso : ∀ n, 0 < n → ∀ a a', e n (b n a) (b n a') (ζ n ^ Dw.EF a a')) :
    ∃ I' : TateIso D' K Q act e, (∀ n, I'.ζ n = ζ n) ∧ ∀ n, 0 < n → ∀ a, b n a = I'.ev n (f a) := by
  have := D'.proj
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf.1
  have hs' : ∀ w, f (s w) = w := fun w => LinearMap.congr_fun hs w
  have hiso' : ∀ n, 0 < n → ∀ a w', e n (b n a) (b n (s w')) (ζ n ^ D'.EF (f a) w') := fun n hn a w' => by
    have h := hiso n hn a (s w')
    rwa [← hf.2.2, hs'] at h
  have hiso'' : ∀ n, 0 < n → ∀ w w', e n (b n (s w)) (b n (s w')) (ζ n ^ D'.EF w w') := fun n hn w w' => by
    have h := hiso' n hn (s w) w'
    rwa [hs'] at h
  have hadd' : ∀ n, 0 < n → ∀ w w', b n (s (w + w')) = b n (s w) * b n (s w') := fun n hn w w' => by
    rw [map_add, hadd n hn]
  have hko := fun n (hn : 0 < n) => TorsIsometry.ker_and_onto E H D' K Q (e n) n (ζ n) (fun w => b n (s w)) hn
    (hcard n hn) (fun y c _ => hone n y c) (hζ n hn) (hadd' n hn) (fun w => hpow n hn _) (hiso'' n hn)
  refine ⟨{ ζ := ζ, ζ_prim := hζ, ζ_pow := hζ', ev := fun n w => if 0 < n then b n (s w) else 1
            add := fun n w w' => ?_, lin := fun n c w => ?_, ker := fun n hn => ?_, onto := fun n hn => ?_
            tower := fun n m hn hm w => ?_, isom := fun n hn w w' => ?_ }, fun _ => rfl, fun n hn a => ?_⟩
  · split_ifs with hn
    · exact hadd' n hn w w'
    · exact (_root_.mul_one _).symm
  · split_ifs with hn
    · rw [map_smul, hlin n hn]
    · exact (hact c).symm
  · simp only [if_pos hn]
    exact (hko n hn).1
  · simp only [if_pos hn]
    exact (hko n hn).2
  · simp only [if_pos hn, if_pos (Nat.mul_pos hn hm)]
    exact htow n m hn hm _
  · simp only [if_pos hn]
    exact hiso'' n hn w w'
  · show _ = if 0 < n then b n (s (f a)) else 1
    rw [if_pos hn]
    obtain ⟨w, hw⟩ := ((hko n hn).2 _).1 (hpow n hn a)
    obtain ⟨c, hc⟩ := TorsIsometry.exists_eq_nsmul_of_dvd D'.EF D'.unimod n (f a - w) fun w' => by
      have h₁ := hiso' n hn a w'
      rw [← hw] at h₁
      have h₂ := huniq _ _ _ _ _ h₁ (hiso'' n hn w w')
      rw [map_sub, LinearMap.sub_apply, ← (hζ n hn).zpow_eq_one_iff_dvd, zpow_sub, h₂, mul_inv_cancel]
    have h₃ : b n (s (f a - w)) = 1 := ((hko n hn).1 _).2 ⟨c, hc⟩
    have h₄ := hadd' n hn (f a - w) w
    rw [sub_add_cancel, h₃, _root_.one_mul] at h₄
    exact hw.symm.trans h₄.symm

section Pairs

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

attribute [local instance] TorusExt.gtGroup

theorem eq_of_equiv (hB : D.TauBimult) {k : ℕ} (hk : 0 < k) {p q : QkPt D F k} (h : QkPt.Equiv D F p q)
    (hy : p.y = q.y) : p = q := by
  obtain ⟨z, h₁, h₂⟩ := (TorusExt.equiv_iff hB _ _).1 h
  have hz : k • z = 0 := by
    rw [hy] at h₁
    exact left_eq_add.1 h₁
  have : z = 0 := by
    rw [← natCast_zsmul] at hz
    exact (smul_eq_zero.1 hz).resolve_left (Int.natCast_ne_zero.2 hk.ne')
  subst this
  rw [map_zero, add_zero] at h₂
  exact TorusExt.qk_ext hy h₂.symm

theorem b_pow (hB : D.TauBimult) {k : ℕ} (p : QkPt D F k) (hy : p.y = 0) : p.g.b ^ k = 1 := by
  rw [← TorusExt.nsmul_b, TorusExt.qk_nsmul hB, hy, map_zero, TorusExt.zero_b]

theorem b_tower (hB : D.TauBimult) {n m : ℕ} (hn : 0 < n) {p p₀ : QkPt D F (n * m)} {q r r₀ : QkPt D F n}
    (hp : QkPt.Equiv D F p p₀) (hp₀ : p₀.y = 0) (hq : q.y = p.y) (hg : GtPtF.IsNsmul m p.g q.g)
    (hr : QkPt.Equiv D F q r) (hr' : QkPt.Equiv D F r r₀) (hr₀ : r₀.y = 0) : p₀.g.b ^ m = r₀.g.b := by
  obtain ⟨z, h₁, h₂⟩ := (TorusExt.equiv_iff hB _ _).1 hp
  have h₃ : TorusExt.qkShift hB q (m • z) = r₀ := by
    refine eq_of_equiv hB hn (TorusExt.equiv_trans hB (TorusExt.equiv_symm hB (TorusExt.equiv_qkShift hB q _))
      (TorusExt.equiv_trans hB hr hr')) ?_
    show q.y + n • m • z = r₀.y
    rw [hr₀, hq, smul_smul, ← h₁, hp₀]
  rw [← h₃, ← TorusExt.nsmul_b, h₂, nsmul_add, ← (TorusExt.isNsmul_iff_eq _ _ _).1 hg, ← map_nsmul]
  rfl

end Pairs

attribute [local instance] TorusExt.gtGroup in

theorem exists_gradedTateIso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw D' : Datum H) (Z : Submodule (𝓞 E) Dw.La)
  (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La), GlobalTheory.LowDat.IsLower Dw D' Z f →
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R →
  ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
  Module.finrank ℤ D'.La = 2 * P.D.toPre.P.g →
  ∀ I : (letI := H.starRing; TateIsoQ Dw P.D.toPre P.oD F),
  (∀ n, 0 < n → ∀ a : GlobalTheory.LowDat.perp Dw Z, ∃ q : QkPt P.D.toPre F n, QkPt.Equiv P.D.toPre F (I.ev n a) q ∧ q.y = 0) →
  ∃ I' : TateIso D' F (TF (R := R) F ⟶ P.D.toPre.P.A) (fun a g => g ≫ (letI := H.starRing; P.oD.onB.act a))
      (fun n g g' z => Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n g g' (unitOn z)),
    (∀ n, I'.ζ n = I.ζ n) ∧ ∀ n, 0 < n → ∀ (a : GlobalTheory.LowDat.perp Dw Z) (q : QkPt P.D.toPre F n),
      QkPt.Equiv P.D.toPre F (I.ev n a) q → q.y = 0 → q.g.b = I'.ev n (f a) := by
  intro E _ _ _ H Dw D' Z f hf R _ _ _ hR t P F _ _ _ hrk I hI
  letI := H.starRing
  have hB := P.D.tau_bimult
  have hL := GlobalTheory.firstFiveLaws
  have hG := hL.1.globalFns
  have := hR.2
  have := hR.1.1
  have : IsLocallyNoetherian (Spec (CommRingCat.of R)) := inferInstance
  choose q hq hy using hI
  have huniq : ∀ (n : ℕ) (x y : TF (R := R) F ⟶ P.D.toPre.P.A) (c c' : Fˣ),
      Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n x y (unitOn c) →
      Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n x y (unitOn c') → c = c' := fun n x y c c' =>
    weilIs_unique_fieldPoint _ _ _ P.D.toPre.P.isLB F _ n x y c c'
  obtain ⟨I', h₁, h₂⟩ := exists_tateIso_of_perp Dw D' Z f hf F (TF (R := R) F ⟶ P.D.toPre.P.A)
    (fun a g => g ≫ P.oD.onB.act a)
    (fun n g g' z => Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n g g' (unitOn z)) I.ζ I.ζ_prim I.ζ_pow
    (fun n a => if hn : 0 < n then (q n hn a).g.b else 1)
    (fun c => by
      have := P.oD.onB.hom c
      exact MonObj.one_comp _)
    (fun n hn => by
      have : NeZero n := ⟨hn.ne'⟩
      rw [hrk]
      exact (hL.1.mulN _ P.D.toPre.P n hn).2.2.2.2 F _
        (IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim n hn)).neZero'.ne)
    huniq
    (fun n y c h => by
      have h₁ := (hL.1.weil _ P.D.toPre.P n _).2.1 _ _ _ _ _ h h
      rw [_root_.mul_one] at h₁
      have e : unitOn (c * c) = unitOn c * unitOn c := map_mul _ _ _
      exact mul_eq_left.1 (huniq n 1 y _ _ (e ▸ h₁) h))
    (fun n hn a a' => by
      simp only [dif_pos hn]
      have h := (TorusExt.qkAdd_iff hB _ _ _).1
        ((TorusExt.qkAdd_iff_of_equiv hB (hq n hn a) (hq n hn a') (I.add n hn a a')).2 (hq n hn (a + a')))
      rw [← eq_of_equiv hB hn h (by
        show (q n hn a).y + (q n hn a').y = _
        rw [hy, hy, hy, add_zero])]
      exact TorusExt.add_b _ _)
    (fun n hn c a => by
      simp only [dif_pos hn]
      have h := (TorusExt.qkAct_iff hB hG P.oD _ _ _).1
        ((TorusExt.qkAct_iff_of_equiv hB hG P.oD (hq n hn a) (I.lin n hn c a)).2 (hq n hn (c • a)))
      rw [← eq_of_equiv hB hn h (by
        show c • (q n hn a).y = _
        rw [hy, hy, smul_zero])]
      exact TorusExt.gtSmul_b hG P.oD _ _)
    (fun n hn a => by
      simp only [dif_pos hn]
      exact b_pow hB _ (hy n hn a))
    (fun n m hn hm a => by
      simp only [dif_pos hn, dif_pos (Nat.mul_pos hn hm)]
      obtain ⟨r, r₁, r₂, r₃⟩ := I.tower n m hn hm a
      exact b_tower hB hn (hq _ _ a) (hy _ _ a) r₁ r₂ r₃ (hq n hn a) (hy n hn a))
    (fun n hn a a' => by
      simp only [dif_pos hn]
      exact (UT.WeilAbelianPart.weilQkIs_iff_weilIs_abelianPart hL R _ hR.1 P.D F n hn _ _ (hy n hn a) (hy n hn a')
        _).1 (PhiOperatorCompare.weilQkIs_of_equiv hB (hq n hn a) (hq n hn a') (I.isom n hn a a')))
  refine ⟨I', h₁, fun n hn a r hr hr₀ => ?_⟩
  rw [← h₂ n hn a, dif_pos hn, eq_of_equiv hB hn
    (TorusExt.equiv_trans hB (TorusExt.equiv_symm hB hr) (hq n hn a)) (hr₀.trans (hy n hn a).symm)]

end GlobalTheory.LowDat.GradedTate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatV
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatVAlg
open GlobalTheory.KS GlobalTheory.HeatGlue

variable {Y X : Scheme.{0}}

theorem pbT_id {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) : pbT (𝟙 Y) s O = rsT s O := by
  rw [pbT_of_le (𝟙 Y) h, rsT_of_le h]
  rfl

theorem cst_eq (π : Y ⟶ X) (V : X.Opens) {O : Y.Opens} (h : O ≤ π ⁻¹ᵁ V) (r : Γ(X, V)) :
    GlobalTheory.HeatV.cst π V h r = pbT π r O := (pbT_of_le π h r).symm

theorem rsT_unit {O₀ O : Y.Opens} (h : O ≤ O₀) (w : Γ(Y, O₀)ˣ) : rsT w.val O * rsT w⁻¹.val O = 1 := by
  rw [← rsT_mul, Units.mul_inv, rsT_one h]

theorem rsT_cocycle (L : LB Y) (hL : L.IsLB) (i j k : L.ι) {O : Y.Opens} (hO : O ≤ L.U i ⊓ L.U j ⊓ L.U k) :
    rsT (L.g i j).val O * rsT (L.g j k).val O = rsT (L.g i k).val O := by
  have e := congrArg (fun u : Γ(Y, L.U i ⊓ L.U j ⊓ L.U k)ˣ => rsT u.val O) (hL.cocycle i j k)
  simp only [Units.val_mul, rsT_mul] at e
  have r : ∀ {V V' : Y.Opens} (h : V' ≤ V) (u : Γ(Y, V)ˣ), O ≤ V' →
      rsT (ReciprocityTheory.ChartRestriction.G.Semi.res h u).val O = rsT u.val O := fun h u hO' => by
    show rsT (resG Y h u.val) O = _
    rw [← rsT_of_le h, rsT_rsT h hO']
  rw [r _ _ hO, r _ _ hO, r _ _ hO] at e
  exact e

theorem exists_heatV : ∀ (Y X : Scheme.{0}) (π : Y ⟶ X) (V : X.Opens) (L : LB Y), L.IsLB → IsUnit (2 : Γ(X, V)) → ∀ (n : ℕ) (dd : Fin n → Fld Y), (∀ a, IsField ⊤ (dd a)) → (∀ a O (h : O ≤ π ⁻¹ᵁ V) (r : Γ(X, V)), dd a O (GlobalTheory.HeatV.cst π V h r) = 0) → ∀ (Θ : Matrix (Fin n) (Fin n) Γ(X, V)), Θᵀ = Θ → ∀ (J : Type) (W : J → Y.Opens) (j : J → L.ι) (d : J → Fld Y) (hW : ∀ i, W i ≤ π ⁻¹ᵁ V), (∀ i, W i ≤ L.U (j i)) → (∀ i, IsField (W i) (d i)) → (∀ i i' O (h : O ≤ W i ⊓ W i') (f : Γ(Y, O)), d i O f - d i' O f = ∑ a, ∑ b, GlobalTheory.HeatV.cst π V (h.trans (inf_le_left.trans (hW i))) (Θ a b) * (dd b O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O) * dd a O f) → (∀ z : C1 W, IsCoc W z → ∃ (cc : Fin n → Γ(X, V)) (y : ∀ i, Γ(Y, W i)), ∀ i i', z i i' = ∑ b, GlobalTheory.HeatV.cst π V (inf_le_left.trans (hW i)) (cc b) * (dd b (W i ⊓ W i') (rsT (L.g (j i) (j i')).val (W i ⊓ W i')) * rsT (L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) + (rsT (y i') (W i ⊓ W i') - rsT (y i) (W i ⊓ W i'))) → ∃ (e u : Fin n → Γ(X, V)) (pf pf' : ∀ i, Γ(Y, W i)), ∀ (k : ℕ) i i' O (h : O ≤ W i ⊓ W i') (f : Γ(Y, O)), GlobalTheory.HeatV.opV π V dd Θ u (fun O' f' => d i O' f' + ∑ a, pbT π (e a) O' * dd a O' f') (pf i) (pf' i) k O (h.trans (inf_le_left.trans (hW i))) (pbT (𝟙 Y) (L.g (j i) (j i')).val O ^ k * f) = pbT (𝟙 Y) (L.g (j i) (j i')).val O ^ k * GlobalTheory.HeatV.opV π V dd Θ u (fun O' f' => d i' O' f' + ∑ a, pbT π (e a) O' * dd a O' f') (pf i') (pf' i') k O (h.trans (inf_le_right.trans (hW i'))) f := by
  intro Y X π V L hL h2 n dd hddF _hddC Θ hΘ J W j d hW hWL hdF hKS hH1
  simp only [cst_eq] at hKS hH1
  have hdd : ∀ a (O : Y.Opens), IsDer (dd a O) := fun a O => isDer_of_isField (hddF a) le_top
  obtain ⟨t, ht⟩ : ∃ t : Γ(X, V), 2 * t = 1 := ⟨_, h2.mul_val_inv⟩
  have hc2 : ∀ O : Y.Opens, O ≤ π ⁻¹ᵁ V → 2 * pbT π t O = 1 := fun O hO => by
    have e := congrArg (fun s => pbT π s O) ht
    simp only [pbT_mul, pbT_one π hO] at e
    rw [show (2 : Γ(X, V)) = 1 + 1 from one_add_one_eq_two.symm, pbT_add, pbT_one π hO, one_add_one_eq_two] at e
    exact e
  have hs : ∀ (O : Y.Opens) a b, pbT π (Θ a b) O = pbT π (Θ b a) O := fun O a b => by
    rw [show Θ a b = Θᵀ b a from rfl, hΘ]
  have hV2 : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' → O ≤ π ⁻¹ᵁ V := fun i i' O h => h.trans (inf_le_left.trans (hW i))
  have hm2 : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' → O ≤ L.U (j i) ⊓ L.U (j i') := fun i i' O h =>
    le_inf (h.trans (inf_le_left.trans (hWL i))) (h.trans (inf_le_right.trans (hWL i')))
  have hm3 : ∀ i i' i'' (O : Y.Opens), O ≤ W i ⊓ W i' ⊓ W i'' → O ≤ L.U (j i) ⊓ L.U (j i') ⊓ L.U (j i'') :=
    fun i i' i'' O h => le_inf (le_inf (h.trans (inf_le_left.trans (inf_le_left.trans (hWL i))))
      (h.trans (inf_le_left.trans (inf_le_right.trans (hWL i'))))) (h.trans (inf_le_right.trans (hWL i'')))
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin n → J → J → ∀ O : Y.Opens, Γ(Y, O), ∀ b i i' O,
      φ b i i' O = dd b O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O := ⟨_, fun _ _ _ _ => rfl⟩
  have rφ : ∀ b i i' (O₁ O : Y.Opens), O₁ ≤ W i ⊓ W i' → O ≤ O₁ → rsT (φ b i i' O₁) O = φ b i i' O := by
    intro b i i' O₁ O h1 h
    rw [hφ, hφ, rsT_mul, ← field_rsT (hddF b) le_top h, rsT_rsT (hm2 i i' O₁ h1) h, rsT_rsT (hm2 i i' O₁ h1) h]
  have dlc : ∀ i i' i'' (O : Y.Opens) (δ : Γ(Y, O) → Γ(Y, O)), IsDer δ → O ≤ W i ⊓ W i' ⊓ W i'' →
      δ (rsT (L.g (j i) (j i'')).val O) * rsT (L.g (j i) (j i''))⁻¹.val O =
        δ (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O +
        δ (rsT (L.g (j i') (j i'')).val O) * rsT (L.g (j i') (j i''))⁻¹.val O := by
    intro i i' i'' O δ hδ hO
    have h3 := hm3 i i' i'' O hO
    exact hδ.dlog_mul (rsT_unit (h3.trans inf_le_left) _)
      (rsT_unit (le_inf (h3.trans (inf_le_left.trans inf_le_right)) (h3.trans inf_le_right)) _)
      (rsT_unit (le_inf (h3.trans (inf_le_left.trans inf_le_left)) (h3.trans inf_le_right)) _)
      (rsT_cocycle L hL _ _ _ h3)
  have cφ : ∀ b i i' i'' (O : Y.Opens), O ≤ W i ⊓ W i' ⊓ W i'' →
      φ b i i'' O = φ b i i' O + φ b i' i'' O := fun b i i' i'' O hO => by
    rw [hφ, hφ, hφ]; exact dlc i i' i'' O _ (hdd b O) hO
  have ks : ∀ i i' i'' (O : Y.Opens), O ≤ W i ⊓ W i' →
      d i O (rsT (L.g (j i') (j i'')).val O) * rsT (L.g (j i') (j i''))⁻¹.val O =
        d i' O (rsT (L.g (j i') (j i'')).val O) * rsT (L.g (j i') (j i''))⁻¹.val O +
        ∑ a, ∑ b, pbT π (Θ a b) O * φ b i i' O * φ a i' i'' O := fun i i' i'' O hO => by
    rw [← sub_eq_iff_eq_add', ← sub_mul, hKS i i' O hO, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hφ, hφ]; ring

  obtain ⟨z₁, hz₁⟩ : ∃ z : C1 W, ∀ i i', z i i' =
      -(pbT π t (W i ⊓ W i') * ∑ a, ∑ b, pbT π (Θ a b) (W i ⊓ W i') *
          dd a (W i ⊓ W i') (φ b i i' (W i ⊓ W i'))) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨z₂, hz₂⟩ : ∃ z : C1 W, ∀ i i', z i i' =
      d i (W i ⊓ W i') (rsT (L.g (j i) (j i')).val (W i ⊓ W i')) * rsT (L.g (j i) (j i'))⁻¹.val (W i ⊓ W i') -
        pbT π t (W i ⊓ W i') * ∑ a, ∑ b, pbT π (Θ a b) (W i ⊓ W i') *
          φ a i i' (W i ⊓ W i') * φ b i i' (W i ⊓ W i') := ⟨_, fun _ _ => rfl⟩
  have rz₁ : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' → rsT (z₁ i i') O =
      -(pbT π t O * ∑ a, ∑ b, pbT π (Θ a b) O * dd a O (φ b i i' O)) := by
    intro i i' O hO
    have e : ∀ a b, rsT (dd a (W i ⊓ W i') (φ b i i' (W i ⊓ W i'))) O = dd a O (φ b i i' O) := fun a b => by
      rw [← field_rsT (hddF a) le_top hO, rφ b i i' _ O le_rfl hO]
    rw [hz₁]
    simp only [rsT_neg, rsT_mul, rsT_sum, rsT_pbT π (hV2 i i' _ le_rfl) hO, e]
  have rz₂ : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' → rsT (z₂ i i') O =
      d i O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O -
        pbT π t O * ∑ a, ∑ b, pbT π (Θ a b) O * φ a i i' O * φ b i i' O := by
    intro i i' O hO
    have e : ∀ b, rsT (φ b i i' (W i ⊓ W i')) O = φ b i i' O := fun b => rφ b i i' _ O le_rfl hO
    rw [hz₂]
    simp only [rsT_sub, rsT_mul, rsT_sum, rsT_pbT π (hV2 i i' _ le_rfl) hO, e]
    rw [← field_rsT (hdF i) inf_le_left hO, rsT_rsT (hm2 i i' _ le_rfl) hO, rsT_rsT (hm2 i i' _ le_rfl) hO]
  have tri : ∀ i i' i'', (W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') ∧ (W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') ∧
      (W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') :=
    fun _ _ _ => ⟨inf_le_left, le_inf (inf_le_left.trans inf_le_right) inf_le_right,
      le_inf (inf_le_left.trans inf_le_left) inf_le_right⟩
  have coc₁ : IsCoc W z₁ := by
    intro i i' i''
    obtain ⟨t1, t2, t3⟩ := tri i i' i''
    rw [rz₁ i i' _ t1, rz₁ i' i'' _ t2, rz₁ i i'' _ t3]
    have e := fun b => cφ b i i' i'' _ le_rfl
    simp only [e, (hdd _ _).1, mul_add, Finset.sum_add_distrib]
    ring
  have coc₂ : IsCoc W z₂ := by
    intro i i' i''
    obtain ⟨t1, t2, t3⟩ := tri i i' i''
    rw [rz₂ i i' _ t1, rz₂ i' i'' _ t2, rz₂ i i'' _ t3]
    have e := fun b => cφ b i i' i'' _ le_rfl
    simp only [e]
    rw [dlc i i' i'' _ _ (isDer_of_isField (hdF i) (t1.trans inf_le_left)) le_rfl, ks i i' i'' _ t1,
      quad_add (hs _) (fun a => φ a i i' _) (fun a => φ a i' i'' _)]
    linear_combination (∑ a, ∑ b, pbT π (Θ a b) (W i ⊓ W i' ⊓ W i'') * φ b i i' _ * φ a i' i'' _) *
      hc2 _ (hV2 i i' _ t1)
  obtain ⟨c, y₁, hy₁⟩ := hH1 z₁ coc₁
  obtain ⟨e, y₂, hy₂⟩ := hH1 z₂ coc₂
  have A1 : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' →
      rsT (y₁ i') O - rsT (y₁ i) O = -(pbT π t O * ∑ a, ∑ b, pbT π (Θ a b) O * dd a O (φ b i i' O)) -
        ∑ b, pbT π (c b) O * φ b i i' O := by
    intro i i' O hO
    have h := congrArg (fun s => rsT s O) (hy₁ i i')
    simp only [rz₁ i i' O hO, rsT_add, rsT_sub, rsT_sum, rsT_mul, rsT_pbT π (hV2 i i' _ le_rfl) hO,
      rsT_rsT inf_le_left hO, rsT_rsT inf_le_right hO] at h
    have e' : ∀ b, rsT (dd b (W i ⊓ W i') (rsT (L.g (j i) (j i')).val (W i ⊓ W i')) *
        rsT (L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) O = φ b i i' O := fun b => by
      rw [← hφ, rφ b i i' _ O le_rfl hO]
    simp only [← rsT_mul, e'] at h
    linear_combination -h
  have A2 : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' →
      rsT (y₂ i') O - rsT (y₂ i) O = d i O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O -
        pbT π t O * ∑ a, ∑ b, pbT π (Θ a b) O * φ a i i' O * φ b i i' O - ∑ b, pbT π (e b) O * φ b i i' O := by
    intro i i' O hO
    have h := congrArg (fun s => rsT s O) (hy₂ i i')
    simp only [rz₂ i i' O hO, rsT_add, rsT_sub, rsT_sum, rsT_mul, rsT_pbT π (hV2 i i' _ le_rfl) hO,
      rsT_rsT inf_le_left hO, rsT_rsT inf_le_right hO] at h
    have e' : ∀ b, rsT (dd b (W i ⊓ W i') (rsT (L.g (j i) (j i')).val (W i ⊓ W i')) *
        rsT (L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) O = φ b i i' O := fun b => by
      rw [← hφ, rφ b i i' _ O le_rfl hO]
    simp only [← rsT_mul, e'] at h
    linear_combination -h
  refine ⟨fun a => -e a, fun a => -c a, y₂, y₁, ?_⟩
  intro k i i' O h f
  have hO : O ≤ π ⁻¹ᵁ V := hV2 i i' O h
  rw [pbT_id (hm2 i i' O h)]
  have hg := rsT_unit (hm2 i i' O h) (L.g (j i) (j i'))
  have hdi : IsDer (fun f : Γ(Y, O) => d i O f + ∑ a, pbT π (-e a) O * dd a O f) := by
    have h1 := isDer_of_isField (hdF i) (h.trans inf_le_left)
    refine ⟨fun x y => ?_, fun x y => ?_⟩
    · simp only [h1.1, (hdd _ O).1, mul_add, Finset.sum_add_distrib]
      ring
    · have s : ∑ a, pbT π (-e a) O * (x * dd a O y + y * dd a O x) =
          x * ∑ a, pbT π (-e a) O * dd a O y + y * ∑ a, pbT π (-e a) O * dd a O x := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => by ring
      simp only [h1.2, (hdd _ O).2, s]
      ring
  have key := ringOp_conj hdi (fun a => hdd a O) (Θ := Θ.map (GlobalTheory.HeatV.cst π V hO))
    (fun a b => by show GlobalTheory.HeatV.cst π V hO (Θ a b) = GlobalTheory.HeatV.cst π V hO (Θ b a)
                   rw [show Θ a b = Θᵀ b a from rfl, hΘ])
    (fun a => GlobalTheory.HeatV.cst π V hO (-c a)) (rsT (y₂ i) O) (rsT (y₁ i) O) hg k f
  refine key.trans ?_
  congr 1
  have F1 := hKS i i' O h f
  have F2 := A2 i i' O h
  have F3 := A1 i i' O h
  simp only [hφ] at F2 F3
  simp only [ringOp, GlobalTheory.HeatV.opV, Matrix.map_apply, cst_eq]
  have E : (d i O (rsT (L.g (j i) (j i')).val O) + ∑ a, pbT π (-e a) O * dd a O (rsT (L.g (j i) (j i')).val O)) *
      rsT (L.g (j i) (j i'))⁻¹.val O = d i O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O -
        ∑ b, pbT π (e b) O * (dd b O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O) := by
    rw [add_mul, Finset.sum_mul, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun b _ => by rw [pbT_neg]; ring
  have U1 : ∑ a, pbT π (-c a) O * (dd a O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O) =
      -∑ b, pbT π (c b) O * (dd b O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by rw [pbT_neg]; ring
  rw [E, U1]
  set g := rsT (L.g (j i) (j i')).val O
  set gi := rsT (L.g (j i) (j i'))⁻¹.val O
  linear_combination (2 * (k : Γ(Y, O))) * F1 +
    (k : Γ(Y, O)) ^ 2 * f * (-2 * F2 + (∑ a, ∑ b, pbT π (Θ a b) O * (dd a O g * gi) * (dd b O g * gi)) * hc2 O hO) +
    (k : Γ(Y, O)) * f * (-2 * F3 + (∑ a, ∑ b, pbT π (Θ a b) O * dd a O (dd b O g * gi)) * hc2 O hO)

end GlobalTheory.HeatVAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationPulledBackTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.TraitPull

theorem exists_pull_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → ∀ h : T.V →+* W, Function.Injective h → IsLocalHom h → ∃ (tW : SAB H (Sp W)) (_ : SABMap tW T.t (spMap h)) (PW : PELUnif (maximalIdeal W) tW) (e : PW.D.toPre.X ≃ₗ[𝓞 E] T.P.D.toPre.X), ∀ y, 0 ≤ T.be (e y) (e y) ∧ ∃ r, PsiCoord PW.D.toPre y r ∧ Associated (r ^ 2) (h T.ϖ ^ (T.be (e y) (e y)).toNat) := by
  intro E _ _ _ H Dw l Xo c T W _ _ _ hW hWd h hi hl
  obtain ⟨tW, ⟨m⟩⟩ := GlobalTheory.Models.Inhab.exists_pull (spMap h) T.t
  obtain ⟨PW, e, he⟩ := GlobalTheory.UnifDvrBaseChange.exists_pelUnif E H T.V T.cdvr T.t T.P W hW hWd h hi hl tW ⟨m⟩
  refine ⟨tW, m, PW, e, fun y => ?_⟩
  obtain ⟨u, n, hn, hc⟩ := T.mono (e y)
  have hn0 : T.be (e y) (e y) = 2 * (n 0 : ℤ) := hn 0
  obtain ⟨v, hv⟩ := he y _ hc
  refine ⟨by rw [hn0]; positivity, _, hv, ?_⟩
  have ht : (T.be (e y) (e y)).toNat = 2 * n 0 := by rw [hn0]; omega
  rw [ht]
  have hu : IsUnit ((v : W) * h u) := v.isUnit.mul (u.isUnit.map h)
  have e1 : ((v : W) * h (u * ∏ i, ![T.ϖ] i ^ n i)) ^ 2 = ((v : W) * h u) ^ 2 * h T.ϖ ^ (2 * n 0) := by
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow]
    ring
  rw [e1]
  exact associated_unit_mul_left _ _ (hu.pow 2)

end GlobalTheory.UPoinc.TraitPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactificationGenericSubsetModuli
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem ker_eq_bot_of_charZero {o K : Type} [CommRing o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field K]
    [CharZero K] (φ : o →+* K) : RingHom.ker φ = ⊥ := by
  by_contra h
  haveI : (RingHom.ker φ).IsMaximal := (RingHom.ker_isPrime φ).isMaximal h
  letI := Ideal.Quotient.field (RingHom.ker φ)
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : Module.Finite ℤ (o ⧸ RingHom.ker φ) := finite_of_finite_type_of_isJacobsonRing ℤ _
  haveI : CharZero (o ⧸ RingHom.ker φ) := (RingHom.charZero_iff (RingHom.kerLift_injective φ)).2 inferInstance
  exact Int.not_isField (isField_of_isIntegral_of_isField (R := ℤ) (S := o ⧸ RingHom.ker φ)
    (fun _ _ h => Int.cast_injective (α := o ⧸ RingHom.ker φ) (by simpa using h)) (Field.toIsField _))

theorem UCompact.range_subset_generic {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} (C : UCompact Xo c) {K : Type} [Field K] [CharZero K]
    (x : Sp K ⟶ Sp C.o) : Set.range x ⊆ Set.range (spMap C.b) := by
  haveI := C.ded
  haveI := C.ft
  obtain ⟨φ, rfl⟩ := Spec.map_surjective x
  rintro _ ⟨w, rfl⟩
  refine ⟨(⊥ : PrimeSpectrum c.F), PrimeSpectrum.ext ?_⟩
  show Ideal.comap C.b ⊥ = Ideal.comap φ.hom w.asIdeal
  rw [Subsingleton.elim w (⊥ : PrimeSpectrum K)]
  exact ((RingHom.injective_iff_ker_eq_bot _).1 C.inj).trans (ker_eq_bot_of_charZero (K := K) φ.hom).symm

theorem exists_open_generic_subset_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∃ W : C.Z.Opens, Set.range C.i ⊆ W ∧ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z), Set.range (gPt p ≫ y) ⊆ W → Set.range (gPt p ≫ y) ⊆ Set.range C.i := by
  intro E _ _ _ H Dw l Xo c C
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.iF_open
  haveI := C.ded
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hg : Topology.IsEmbedding (pullback.fst C.z (spMap C.b) :) := (pullback.fst C.z (spMap C.b)).isEmbedding
  obtain ⟨U, hU, hUe⟩ := hg.isInducing.isOpen_iff.1 C.iF.isOpenEmbedding.isOpen_range
  refine ⟨⟨U, hU⟩, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    have : C.iF x ∈ (pullback.fst C.z (spMap C.b) :) ⁻¹' U := hUe ▸ ⟨x, rfl⟩
    exact this
  · intro p _ y hy
    rintro _ ⟨w, rfl⟩
    have h1 : (gPt p ≫ y) w ∈ Set.range (pullback.fst C.z (spMap C.b) :) := by
      rw [Scheme.Pullback.range_fst]
      exact C.range_subset_generic ((gPt p ≫ y) ≫ C.z) ⟨w, rfl⟩
    obtain ⟨t, ht⟩ := h1
    have h2 : t ∈ (pullback.fst C.z (spMap C.b) :) ⁻¹' U := by
      show _ ∈ U
      rw [ht]
      exact hy ⟨w, rfl⟩
    rw [hUe] at h2
    obtain ⟨x, rfl⟩ := h2
    exact ⟨x, ht⟩

end GlobalTheory.UPoinc
end

