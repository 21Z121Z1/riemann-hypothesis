import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SmulPeriodMapMkZeroFstEqNegForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0028
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaSectionsExtendGermRingsAndSpanFibres
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TwoRigidifiedThetaFramesOnFibre

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFptsPull
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.FibrePull

section Val
variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {A : Type} [CommRing A] [IsLocalRing A]

abbrev wv (w : LB.Iso L' (L.pull F)) (x : Sp A ⟶ X') (j : L.ι) (k : L'.ι) : A :=
  valR x ((LB.div (L.pull F) L').U (fun _ => j, k)) (w.s (fun _ => j, k)).val

omit [IsLocalRing A] in
theorem le_div_iff (x : Sp A ⟶ X') (j : L.ι) (k : L'.ι) :
    ⊤ ≤ x ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, k) ↔ ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j ∧ ⊤ ≤ x ⁻¹ᵁ L'.U k :=
  ⟨fun h => ⟨fun _ hz => mem_pull.1 (h hz).1, fun _ hz => (h hz).2⟩,
    fun h _ hz => ⟨mem_pull.2 (h.1 hz), h.2 hz⟩⟩

theorem exists_chart_pt (hL : L.IsLB) (x : Sp A ⟶ X) : ∃ j, ⊤ ≤ x ⁻¹ᵁ L.U j := by
  obtain ⟨j, hj⟩ := exists_chart hL (x (cpt A))
  exact ⟨j, (top_le_iff_cpt x _).2 hj⟩

omit [IsLocalRing A] in
theorem toStkA_wv (w : LB.Iso L' (L.pull F)) (x : Sp A ⟶ X') {j : L.ι} {k : L'.ι} (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ L'.U k) (z : Sp A) : toStkA z (wv w x j k) = (gw w x z j k).val :=
  toStkA_valR x _ z ((le_div_iff x j k).2 ⟨hj, hk⟩) _

omit [IsLocalRing A] in
theorem isUnit_wv (w : LB.Iso L' (L.pull F)) (x : Sp A ⟶ X') {j : L.ι} {k : L'.ι} (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ L'.U k) : IsUnit (wv w x j k) :=
  FormalValue.isUnit_valR x _ ((le_div_iff x j k).2 ⟨hj, hk⟩) _

theorem wv_trans {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (x : Sp A ⟶ X') {j j' : L.ι} {k k' : L'.ι}
    (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j') (hk : ⊤ ≤ x ⁻¹ᵁ L'.U k) (hk' : ⊤ ≤ x ⁻¹ᵁ L'.U k') :
    wv w x j k * valR x (L'.U k ⊓ L'.U k') (L'.g k k').val =
      valR (x ≫ F) (L.U j ⊓ L.U j') (L.g j j').val * wv w x j' k' := by
  apply toStkA_injective
  rw [map_mul, map_mul, toStkA_wv w x hj hk, toStkA_wv w x hj' hk',
    toStkA_valR x (L'.U k ⊓ L'.U k') _ (fun _ hz => ⟨hk hz, hk' hz⟩),
    toStkA_valR (x ≫ F) (L.U j ⊓ L.U j') _ (fun _ hz => ⟨hj hz, hj' hz⟩),
    (isGen_iff w).1 hw _ x (cpt A) j j' k k' (hj trivial) (hj' trivial) (hk trivial) (hk' trivial),
    ← Units.val_mul, ← Units.val_mul, mul_right_comm, inv_mul_cancel_right]

theorem valR_g_self (hL : L.IsLB) (x : Sp A ⟶ X) {j : L.ι} (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valR x (L.U j ⊓ L.U j) (L.g j j).val = 1 := by
  apply toStkA_injective
  rw [toStkA_valR x (L.U j ⊓ L.U j) _ (fun _ hz => ⟨hj hz, hj hz⟩), gm_self hL x _ (hj trivial), map_one, Units.val_one]

theorem exists_frm {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (x : Sp A ⟶ X')
    (τ : L.ι → A) (hτ : IsFrm L (x ≫ F) τ) : ∃ τ' : L'.ι → A, IsFrm L' x τ' ∧
      ∀ j k, ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j → ⊤ ≤ x ⁻¹ᵁ L'.U k → τ j = wv w x j k * τ' k := by
  obtain ⟨j₀, h₀⟩ := exists_chart_pt hL (x ≫ F)
  have key : ∀ k, ⊤ ≤ x ⁻¹ᵁ L'.U k → τ j₀ = wv w x j₀ k * (Ring.inverse (wv w x j₀ k) * τ j₀) := fun k hk => by
    rw [Ring.mul_inverse_cancel_left _ _ (isUnit_wv w x h₀ hk)]
  refine ⟨fun k => Ring.inverse (wv w x j₀ k) * τ j₀, ⟨fun k hk => ?_, fun k k' hkk => ?_⟩, fun j k hj hk => ?_⟩
  · exact (isUnit_ringInverse.2 (isUnit_wv w x h₀ hk)).mul (hτ.1 _ h₀)
  · have hk : ⊤ ≤ x ⁻¹ᵁ L'.U k := fun _ hz => (hkk hz).1
    have hk' : ⊤ ≤ x ⁻¹ᵁ L'.U k' := fun _ hz => (hkk hz).2
    refine (isUnit_wv w x h₀ hk).mul_left_cancel ?_
    rw [← key k hk, ← _root_.mul_assoc, wv_trans hw x h₀ h₀ hk hk', valR_g_self hL _ h₀, _root_.one_mul, ← key k' hk']
  · have e := wv_trans hw x hj h₀ hk hk
    rw [valR_g_self hL' _ hk, _root_.mul_one] at e
    rw [e, _root_.mul_assoc, ← key k hk]
    exact hτ.2 j j₀ (fun _ hz => ⟨hj hz, h₀ hz⟩)

variable {w : LB.Iso L' (L.pull F)} {p' : Y' ⟶ X'} {p : Y ⟶ X} {h : Y' ⟶ Y} {n : ℕ}

abbrev TransportedAlt (w : LB.Iso L' (L.pull F)) (a : SecP L' p' n) (t : SecP L p n) (h : Y' ⟶ Y) : Prop :=
  ConstFam.SecThrough w (K := Fin 1) (fun _ => p') (fun _ => p) (fun _ => (n : ℤ)) a t h

theorem TransportedAlt.sval_eq (hp : p' ≫ F = h ≫ p) {a : SecP L' p' n} {t : SecP L p n} (H : TransportedAlt w a t h) (r : Sp A ⟶ Y')
    {j : L.ι} {k : L'.ι} (hj : ⊤ ≤ ((r ≫ p') ≫ F) ⁻¹ᵁ L.U j) (hk : ⊤ ≤ (r ≫ p') ⁻¹ᵁ L'.U k) :
    ArcPts.sval t (r ≫ h) j = wv w (r ≫ p') j k ^ n * ArcPts.sval a r k := by
  have hj' : ⊤ ≤ ((r ≫ h) ≫ p) ⁻¹ᵁ L.U j := by rwa [Category.assoc, ← hp, ← Category.assoc]
  apply toStkA_injective
  have e := H _ r (cpt A) (fun _ => j) (fun _ => k) (fun _ => hj trivial) (fun _ => hk trivial)
  rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val] at e
  rw [map_mul, map_pow, toStkA_wv w _ hj hk]
  exact (FormalValue.toStkA_valR_eq_gs (r ≫ h) (LB.wchart L (fun _ : Fin 1 => p) (fun _ => j)) _
    (fun _ hz => Set.mem_iInter.2 fun _ => hj' hz) _).trans (e.trans (congrArg _
      (FormalValue.toStkA_valR_eq_gs r (LB.wchart L' (fun _ : Fin 1 => p') (fun _ => k)) _
        (fun _ hz => Set.mem_iInter.2 fun _ => hk hz) _).symm))

theorem TransportedAlt.hasVal_iff (hL : L.IsLB) (hL' : L'.IsLB) (hp : p' ≫ F = h ≫ p) {a : SecP L' p' n} {t : SecP L p n}
    (H : TransportedAlt w a t h) (r : Sp A ⟶ Y') {τ : L.ι → A} {τ' : L'.ι → A}
    (hτ : ∀ j k, ⊤ ≤ ((r ≫ p') ≫ F) ⁻¹ᵁ L.U j → ⊤ ≤ (r ≫ p') ⁻¹ᵁ L'.U k → τ j = wv w (r ≫ p') j k * τ' k) (c : A) :
    HasVal a r τ' c ↔ HasVal t (r ≫ h) τ c := by
  have e : (r ≫ h) ≫ p = (r ≫ p') ≫ F := by rw [Category.assoc, ← hp, ← Category.assoc]
  constructor
  · intro Ha j hj
    rw [e] at hj
    obtain ⟨k, hk⟩ := exists_chart_pt hL' (r ≫ p')
    rw [H.sval_eq hp r hj hk, Ha k hk, hτ j k hj hk]
    ring
  · intro Ht k hk
    obtain ⟨j, hj⟩ := exists_chart_pt hL ((r ≫ p') ≫ F)
    refine ((isUnit_wv w _ hj hk).pow n).mul_left_cancel ?_
    rw [← H.sval_eq hp r hj hk, Ht j (by rwa [e]), hτ j k hj hk]
    ring

theorem TransportedAlt.eq_zero (hL : L.IsLB) (hp : p' ≫ F = h ≫ p) {a : SecP L' p' n} {t : SecP L p n} (H : TransportedAlt w a t h)
    (ht : ∀ i, t.f i = 0) (i) : a.f i = 0 := by
  refine fn_ext fun y hy => ?_
  obtain ⟨j, hj⟩ := exists_chart hL (F (p' y))
  have e := H _ (𝟙 _) y (fun _ => j) i (fun _ => hj) (fun k => Set.mem_iInter.1 hy k)
  have hm : (𝟙 Y' ≫ h) y ∈ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j) := Set.mem_iInter.2 fun _ => by
    show (h ≫ p) y ∈ L.U j
    rw [← hp]; exact hj
  have z₁ : gs (𝟙 Y' ≫ h) y (LB.wchart L (fun _ : Fin 1 => p) (fun _ => j)) (t.f fun _ => j) = 0 := by
    refine (congrArg (gs _ _ _) (ht fun _ => j)).trans ((gs_eq _ _ _ hm _).trans ?_)
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  rw [z₁] at e
  refine ((Units.mul_right_eq_zero _).1 e.symm).trans ?_
  exact ((gs_eq _ _ _ hy _).trans ((congrArg _ (map_zero _)).trans (map_zero _))).symm

theorem exists_thr_up (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) [IsIso h] (hp : p' ≫ F = h ≫ p)
    (a : SecP L' p' n) : ∃ t : SecP L p n, TransportedAlt w a t h := by
  obtain ⟨t₀, h₀⟩ := ConstFam.exists_sec_up ((isGen_iff w).1 hw) hL hL' a
  obtain rfl : p = inv h ≫ p' ≫ F := by rw [hp, IsIso.inv_hom_id_assoc]
  refine ⟨DVR.pullSec L (fun _ => p' ≫ F) _ t₀ (inv h), fun Z r z P Q hP hQ => ?_⟩
  have e : (r ≫ h) ≫ inv h = r := by rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hm : (r ≫ h) z ∈ LB.wchart L (fun _ : Fin 1 => inv h ≫ p' ≫ F) P := Set.mem_iInter.2 fun k => by
    show ((r ≫ h) ≫ inv h ≫ p' ≫ F) z ∈ L.U (P k)
    rw [← Category.assoc, e]; exact hP k
  refine ((gs_res (r ≫ h) z _ hm _).trans
    (gs_pull (r ≫ h) (inv h) z _ (Out.wchart_comp_le L (fun _ => p' ≫ F) (inv h) P hm) _)).trans ?_
  rw [e]
  exact h₀ Z r z P Q (Set.mem_iInter.2 hP) (Set.mem_iInter.2 hQ)

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]

omit [StarRing (𝓞 E)] in

theorem exists_fpts {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) (hw : IsRigIso m.cm t'.PP t.PP w) {F : Type} [Field F] {V : Type}
    [AddCommGroup V] {act : 𝓞 E → V → V} {I : ℕ → Type} {φ : ∀ j, I j → V → F} (y' : Sp F ⟶ S') (y : Sp F ⟶ S)
    (hy : y' ≫ f = y) (Θ : FPts act t y φ) : ∃ Θ' : FPts act t' y' φ,
      (∀ v, (Θ'.x v).left ≫ m.φ = (Θ.x v).left ∧ ∀ j j',
        ⊤ ≤ (Θ'.x v).left ⁻¹ᵁ (LB.div (t.PP.L.pull m.φ) t'.PP.L).U (fun _ => j, j') →
        Θ.τ v j = valR (Θ'.x v).left _ (w.s (fun _ => j, j')).val * Θ'.τ v j') ∧
      ∀ k ψ (p : Over.mk y ⟶ t.G) (p' : Over.mk y' ⟶ t'.G), p'.left ≫ m.φ = p.left → Θ.Lev k p ψ → Θ'.Lev k p' ψ := by
  subst hy
  have hL := t.PP.isLB
  have hL' := t'.PP.isLB
  let ρ : (Over.mk y' ⟶ t'.G) →* (Over.mk (y' ≫ f) ⟶ t.G) := pushHom m.cart (Over.mk y')
  have ρl : ∀ x, (ρ x).left = x.left ≫ m.φ := fun _ => rfl
  have inj : Function.Injective ρ := fun a b e => Over.OverMorphism.ext (m.cart.1.hom_ext
    (congrArg (fun q => q.left) e) ((Over.w a).trans (Over.w b).symm))
  have surj : Function.Surjective ρ := fun b =>
    ⟨Over.homMk (m.cart.1.lift b.left y' (Over.w b)) (m.cart.1.lift_snd _ _ _),
      Over.OverMorphism.ext (m.cart.1.lift_fst _ _ _)⟩
  choose x hx using fun v => surj (Θ.x v)
  have hxl : ∀ v, (x v).left ≫ m.φ = (Θ.x v).left := fun v => congrArg (fun q => q.left) (hx v)
  have sq : IsPullback (pullback.fst t'.G.hom y' ≫ m.φ) (pullback.snd t'.G.hom y') t.G.hom (y' ≫ f) :=
    (IsPullback.of_hasPullback t'.G.hom y').paste_horiz m.cart.1
  let h : pullback t'.G.hom y' ⟶ pullback t.G.hom (y' ≫ f) := sq.isoPullback.hom
  have hp : pullback.fst t'.G.hom y' ≫ m.φ = h ≫ pullback.fst t.G.hom (y' ≫ f) := sq.isoPullback_hom_fst.symm
  have f₁ : ∀ a : Over.mk y' ⟶ t'.G, fib a ≫ pullback.fst t'.G.hom y' = a.left := fun a => pullback.lift_fst _ _ _
  have fh : ∀ a : Over.mk y' ⟶ t'.G, fib a ≫ h = fib (ρ a) := fun a => pullback.hom_ext
    (by rw [Category.assoc, ← hp, ← Category.assoc, f₁]; exact (pullback.lift_fst _ _ _).symm)
    (by rw [Category.assoc, sq.isoPullback_hom_snd]
        exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm)
  choose τ hτ hτw using fun v => exists_frm hw.1 hL hL' (x v).left (Θ.τ v) (by rw [hxl]; exact Θ.frm v)
  choose sig hsig using fun j i => ConstFam.exists_secThrough (K := Fin 1) (φ' := fun _ => pullback.fst t'.G.hom y')
    hw.1 hL hL' (fun _ => hp) (Θ.sig j i)
  have hv : ∀ {n : ℕ} {a : SecP t'.PP.L (pullback.fst t'.G.hom y') n} {b : SecP t.PP.L (pullback.fst t.G.hom (y' ≫ f)) n},
      TransportedAlt w a b h → ∀ v c, HasVal a (fib (x v)) (τ v) c ↔ HasVal b (fib (Θ.x v)) (Θ.τ v) c := fun T v c => by
    rw [← hx v, ← fh]
    exact T.hasVal_iff hL hL' hp _ (by rw [f₁]; exact hτw v) c
  have add : ∀ v v', x (v + v') = x v * x v' := fun v v' => inj (by rw [map_mul, hx, hx, hx, Θ.add])
  have x0 : (x 0).left = y' ≫ eSec t'.G := by
    have : x 0 = 1 := by
      have e := add 0 0
      rw [add_zero] at e
      exact left_eq_mul.1 e
    rw [this]
    show (toUnit _ ≫ η[t'.G]).left = _
    simp [eSec]
  refine ⟨⟨x, add, fun e v => inj ?_, τ, hτ, fun k hk => ?_, sig, fun n hn i v => (hv (hsig n i) v _).2 (Θ.val n hn i v),
    fun n hn s => ?_, fun n hn s hs => ?_⟩, fun v => ⟨hxl v, fun j k hjk => ?_⟩, fun k ψ p p' hpp ⟨l₁, l₂, l₃⟩ => ?_⟩
  · refine Over.OverMorphism.ext ?_
    rw [hx, Θ.lin, ρl, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, hxl]
  · obtain ⟨j, hj⟩ := exists_chart_pt hL ((x 0).left ≫ m.φ)
    refine (isUnit_wv w _ hj hk).mul_left_cancel ?_
    rw [← hτw 0 j k hj hk, Θ.rig j (by rw [← hxl]; exact hj)]
    have P := (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig m.cm.e _
      (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L) (fun _ => rfl)).1 hw.2
    rw [x0] at hj hk ⊢
    have e := P _ y' (cpt F) (fun _ => j) (fun _ => k) (fun _ => hj trivial) (fun _ => hk trivial)
    rw [Fintype.prod_unique, zpow_one, m.base] at e
    have hj' : ⊤ ≤ ((y' ≫ f) ≫ eSec t.G) ⁻¹ᵁ t.PP.L.U j := by
      have := m.cm.e_comm
      rw [m.base] at this
      rw [Category.assoc, ← this, ← Category.assoc]; exact hj
    apply toStkA_injective
    rw [map_mul, toStkA_wv w _ hj hk]
    refine (toStkA_valR (y' ≫ f) _ _ (fun _ hz => mem_pull.2 (hj' hz)) _).trans ((congrArg Units.val e).trans ?_)
    rw [Units.val_mul]
    exact congrArg _ (toStkA_valR y' _ _ (fun _ hz => mem_pull.2 (hk hz)) _).symm
  · obtain ⟨b, hb⟩ := exists_thr_up hw.1 hL hL' hp s
    obtain ⟨N, r, i, hi⟩ := Θ.span n hn b
    exact ⟨N, r, i, fun v => (hv hb v _).2 (hi v)⟩
  · obtain ⟨b, hb⟩ := exists_thr_up hw.1 hL hL' hp s
    exact hb.eq_zero hL hp (Θ.sep n hn b fun v => (hv hb v _).1 (hs v))
  · exact hτw v j k ((le_div_iff _ j k).1 hjk).1 ((le_div_iff _ j k).1 hjk).2
  · obtain rfl : ρ p' = p := Over.OverMorphism.ext hpp
    refine ⟨inj (by rw [map_pow, l₁, map_one]), l₂, fun i i' z j' hj' => ?_⟩
    obtain ⟨j, hj⟩ := exists_chart_pt hL ((x z * p').left ≫ m.φ)
    have e := l₃ i i' z j (by rw [← hx, ← map_mul]; exact hj)
    have hj₁ : ⊤ ≤ ((fib (x z * p') ≫ pullback.fst t'.G.hom y') ≫ m.φ) ⁻¹ᵁ t.PP.L.U j := by rw [f₁]; exact hj
    have hj₂ : ⊤ ≤ (fib (x z * p') ≫ pullback.fst t'.G.hom y') ⁻¹ᵁ t'.PP.L.U j' := by rw [f₁]; exact hj'
    rw [← hx, ← map_mul, ← fh, TransportedAlt.sval_eq hp (hsig k i) _ hj₁ hj₂, TransportedAlt.sval_eq hp (hsig k i') _ hj₁ hj₂,
      _root_.mul_assoc, _root_.mul_assoc] at e
    exact ((isUnit_wv w _ hj₁ hj₂).pow k).mul_left_cancel e

theorem exists_fpts_pull : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l bb s) (y : Sp F ⟶ S) (s' : Sp F ⟶ Sp B) (Θ : FPts act o.t y φ), y ≫ s = s' → ∃ (o' : Obj D l bb s') (m : ObjMap o' o y) (w : LB.Iso o'.t.PP.L (o.t.PP.L.pull m.toSABMap.φ)) (Θ' : FPts act o'.t (𝟙 _) φ), IsRigIso m.toSABMap.cm o'.t.PP o.t.PP w ∧ (∀ v, (Θ'.x v).left ≫ m.toSABMap.φ = (Θ.x v).left ∧ ∀ j j', ⊤ ≤ (Θ'.x v).left ⁻¹ᵁ (LB.div (o.t.PP.L.pull m.toSABMap.φ) o'.t.PP.L).U (fun _ => j, j') → Θ.τ v j = valR (Θ'.x v).left _ (w.s (fun _ => j, j')).val * Θ'.τ v j') ∧ ∀ k ψ (p : Over.mk y ⟶ o.t.G) (p' : Over.mk (𝟙 (Sp F)) ⟶ o'.t.G), 1 ≤ k → p'.left ≫ m.toSABMap.φ = p.left → Θ.Lev k p ψ → Θ'.Lev k p' ψ := by
  intro _ _ E _ _ _ H _ D l B _ bb F _ _ _ V _ act I φ S s o y s' Θ hy
  obtain ⟨o', ⟨m⟩⟩ := obj_pull E H D l B B bb bb (RingHom.id B) S (Sp F) s s' y rfl rfl (by
    rw [hy]; exact (Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm)) o
  obtain ⟨w, h₁, h₂, -⟩ := m.toSABMap.lin
  obtain ⟨Θ', r₁, r₂⟩ := exists_fpts m.toSABMap w ⟨h₁, h₂⟩ (𝟙 _) y (Category.id_comp _) Θ
  exact ⟨o', m, w, Θ', ⟨h₁, h₂⟩, r₁, fun k ψ p p' _ => r₂ k ψ p p'⟩

end GlobalTheory.FibrePull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowMulEqSumConstantExpansion
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstExpSpan

open GlobalTheory.ConstFam GlobalTheory.FieldBaseChange

theorem exists_rep (M : Type) [AddCommGroup M] (j : ℕ) :
    ∃ (C : Type) (rep : C → M), ∀ α, ∃! x, ∃ mu, rep x + j • mu = α := by
  refine ⟨M ⧸ (nsmulAddMonoidHom j : M →+ M).range, Quotient.out, fun α => ⟨QuotientAddGroup.mk α, ?_, ?_⟩⟩
  · obtain ⟨mu, h⟩ := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk α :
      M ⧸ (nsmulAddMonoidHom j : M →+ M).range))
    exact ⟨mu, by rw [show j • mu = _ from h, add_neg_cancel_left]⟩
  · rintro x ⟨mu, rfl⟩
    exact (QuotientAddGroup.out_eq' x).symm.trans (QuotientAddGroup.eq.2 ⟨mu, (neg_add_cancel_left _ _).symm⟩)

def valLin {R Z : Type} [CommRing R] [CommRing Z] [IsLocalRing Z] {Y : Scheme.{0}} (π : Y ⟶ Sp R) (M : LB Y)
    (κ : R →+* Z) (p : Sp Z ⟶ Y) (hp : p ≫ π = spMap κ) (i : M.ι) (hi : ⊤ ≤ p ⁻¹ᵁ M.U i) :
    SecOver π M →ₛₗ[κ] Z where
  toFun s := valR p (M.U i) (LB.Sec.f s i)
  map_add' s t := toStkA_injective (by
    rw [map_add, FormalValue.toStkA_valR_eq_gs _ _ _ hi, FormalValue.toStkA_valR_eq_gs _ _ _ hi,
      FormalValue.toStkA_valR_eq_gs _ _ _ hi]
    exact gs_add p _ _ (hi trivial) _ _)
  map_smul' r s := toStkA_injective (by
    have H : constVal (p ≫ π) (cpt Z) r = toStkA (cpt Z) (κ r) := by
      rw [hp, ← Category.id_comp (spMap κ)]
      exact (constVal_specMap _ κ _ r).trans (gs_eq (𝟙 _) _ ⊤ trivial _)
    rw [smul_eq_mul, map_mul, FormalValue.toStkA_valR_eq_gs _ _ _ hi, FormalValue.toStkA_valR_eq_gs _ _ _ hi, ← H]
    exact gs_smul π p _ _ (hi trivial) r _)

theorem exists_pow_mul_eq_sum : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (j : ℕ) (σ : Out.H0 W.P.U.LG.L j), 1 ≤ j → ∃ (N n : ℕ) (r : Fin n → ℂ⟦X⟧) (s : Fin n → Out.H0 W.P.U.LG.L j), (∀ i, HasConstExp W (s i)) ∧ ∀ (Z : Type) [CommRing Z] [IsLocalRing Z] (κ : ℂ⟦X⟧ →+* Z) (p : Sp Z ⟶ W.t.G.left) (k : W.P.U.LG.L.ι), p ≫ W.t.G.hom = spMap κ → ⊤ ≤ p ⁻¹ᵁ W.P.U.LG.L.U k → κ PowerSeries.X ^ N * FormalValue.secVal W.P.U.toUnifPre σ p k = ∑ i, κ (r i) * FormalValue.secVal W.P.U.toUnifPre (s i) p k := by
  intro hL E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W j σ hj
  have hW : WitData a W.P.D W.P.oD W.φ W.he W.w W.e :=
    ⟨W.spec.1, W.spec.2.1, W.spec.2.2.1, W.spec.2.2.2.1, W.spec.2.2.2.2.1,
      fun F _ _ _ _ uF h₁ h₂ => (W.spec.2.2.2.2.2 F uF h₁ h₂).1⟩
  obtain ⟨C, rep, hrep⟩ := exists_rep a.D₀.X j
  let bas := fun x => Module.Basis.ofVectorSpace ℂ (SecBMod a.D₀ j (rep x))
  have ex := fun i : Σ x, Module.Basis.ofVectorSpaceIndex ℂ (SecBMod a.D₀ j (rep x)) =>
    exists_expandsAt hW hL.globalFns hj W.P.U (rep i.1) (bas i.1 i.2)
  choose m hm using ex
  choose f s hf hE using fun i => hm i (m i) le_rfl
  obtain ⟨N, hN⟩ := exists_pow_smul_mem_span hW hL.globalFns hj W.P.U rep hrep bas m f s hf hE σ
  obtain ⟨n, r, t, ht⟩ := Submodule.mem_span_set'.1 hN
  refine ⟨N, n, r, fun i => (t i).1, fun i => ?_, fun Z _ _ κ p k hp hk => ?_⟩
  · obtain ⟨q, hq⟩ := (t i).2
    refine (congrArg (HasConstExp W) hq).mp ⟨f q, hE q, fun x => ?_⟩
    rcases eq_or_off W.e j (rep q.1) (W.e x) with ⟨mu, h⟩ | h
    · obtain rfl := W.e.injective h
      refine ⟨feTranslate a.D₀ j mu _ (bas q.1 q.2), PowerSeries.X ^ ((m q : ℤ) + expo a j (rep q.1) mu).toNat,
        fun Z _ _ p κ jf j₀ hp hi => ?_⟩
      rw [((hf q).1 mu).2]
      exact ConstThetaSections.valR_smul_pullB hW j _ _ _ Z p κ jf j₀ hp hi
    · refine ⟨(0 : SecBMod a.D₀ j x), 0, fun Z _ _ p κ jf j₀ hp hi => ?_⟩
      rw [(hf q).2 _ h, ← zero_smul ℂ⟦X⟧ (pullB hW j x 0)]
      exact ConstThetaSections.valR_smul_pullB hW j _ _ _ Z p κ jf j₀ hp hi
  · let v := valLin W.t.G.hom
      (LB.LinComb W.P.U.LG.L (K := Fin 1) (fun _ => 𝟙 W.t.G.left) (fun _ => (j : ℤ))) κ p hp (fun _ => k)
      (FormalValue.top_le_secChart hk)
    refine (congrArg (· * _) (map_pow κ _ N).symm).trans ((v.map_smulₛₗ _ σ).symm.trans
      ((congrArg v ht.symm).trans ((map_sum v _ _).trans (Finset.sum_congr rfl fun i _ => v.map_smulₛₗ _ _))))

end GlobalTheory.ConstExpSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSectionValuesFormalThetaSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory.ConstThetaSections

open ConstFam FormalValue

theorem exists_vals_fsum : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (j : ℕ) [NeZero j] (α : Λ.A.X), ∀ th ∈ Λ.A.Theta j α, ∃ (m : ℕ) (σ : Out.H0 W.P.U.LG.L j), Ξ.Vals σ (fun v => HahnSeries.single (m : ℤ) (1 : ℂ) * Λ.A.FSum j α th v) := by
  intro hL hL₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ j _ α th hth
  have hj : 1 ≤ j := NeZero.one_le
  obtain ⟨s₀, hs₀, -⟩ := ((ArcThetaSpaces.sections_theta hL hL₂ E H D l c O β b a Λ).1 j α hj).2 th hth
  have hW : WitData a W.P.D W.P.oD W.φ W.he W.w W.e := ⟨W.spec.1, W.spec.2.1, W.spec.2.2.1, W.spec.2.2.2.1,
    W.spec.2.2.2.2.1, fun F _ _ _ _ uF h₁ h₂ => (W.spec.2.2.2.2.2 F uF h₁ h₂).1⟩
  obtain ⟨m, hm⟩ := exists_expandsAt hW hL.globalFns hj W.P.U (Λ.ε α) s₀
  obtain ⟨f, σ, hf, hE⟩ := hm m le_rfl
  have ex : ∀ mu, expo a j (Λ.ε α) (Λ.ε mu) = Λ.A.exponent j α mu := fun mu => by
    rw [expo, AnArc.exponent, AnArc.q, Λ.be_eq, Λ.be_eq]
  have hpos : ∀ mu, 0 ≤ (m : ℤ) + Λ.A.exponent j α mu := fun mu => ex mu ▸ (hf.1 (Λ.ε mu)).1
  have comp : ∀ mu, ∃ t : SecBMod a.D₀ j (Λ.ε (α + j • mu)), f (W.e (Λ.ε (α + j • mu))) =
      (PowerSeries.X : ℂ⟦X⟧) ^ ((m : ℤ) + Λ.A.exponent j α mu).toNat • pullB hW j _ t ∧
      ∀ z, Λ.fn j (α + j • mu) t z = Λ.A.psi mu ^ j * eTwoPi (Λ.A.T mu α) * th (z + Λ.A.ct mu) := fun mu => by
    have cast : ∀ x, Λ.ε α + j • Λ.ε mu = x → ∃ t : SecBMod a.D₀ j x, f (W.e x) =
        (PowerSeries.X : ℂ⟦X⟧) ^ ((m : ℤ) + Λ.A.exponent j α mu).toNat • pullB hW j _ t ∧
        ∀ z, FrameValue.secVal Λ.u a.D₀.P.isLB t (Λ.u.ex z).left
          ![z, z + (Λ.A.ct α + j • Λ.A.ct mu), Λ.A.ct α + j • Λ.A.ct mu, 0] =
            Λ.A.psi mu ^ j * eTwoPi (Λ.A.T mu α) * th (z + Λ.A.ct mu) := by
      rintro _ rfl
      refine ⟨_, ex mu ▸ (hf.1 (Λ.ε mu)).2, fun z => ?_⟩
      have es := Λ.psi (mu + α)
      rw [map_add Λ.ε, map_add Λ.A.ct] at es
      refine (secVal_feTranslate Λ.ah Λ.rig j (Λ.ct α) (Λ.ct mu) (Λ.psi α) (Λ.psi mu) es s₀ z).trans ?_
      refine (congrArg (· * _) (congrFun hs₀ (z + Λ.A.ct mu))).trans ?_
      have := (Λ.A.psi mu).ne_zero
      have := (Λ.A.psi α).ne_zero
      push_cast
      rw [Λ.A.psi_add]
      field_simp
    obtain ⟨t, h₁, h₂⟩ := cast (Λ.ε (α + j • mu)) (by rw [map_add, map_nsmul])
    refine ⟨t, h₁, fun z => Eq.trans ?_ (h₂ z)⟩
    exact congrArg (fun q => FrameValue.secVal Λ.u a.D₀.P.isLB t (Λ.u.ex z).left ![z, z + q, q, 0])
      ((map_add Λ.A.ct _ _).trans (congrArg _ (map_nsmul Λ.A.ct _ _)))
  refine ⟨m, σ, fun v jL hjL => ?_⟩
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB (basePt (Ξ.g v) (cpt ℂ⟦X⟧))
  obtain ⟨j₀, h₀⟩ := exists_chart a.D₀.P.isLB (W.φ (basePt (Ξ.g v) (cpt ℂ⟦X⟧)))
  have hM' := (top_le_iff_cpt _ _).2 hM
  have hw : ⊤ ≤ (Ξ.g v).b.left ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) :=
    (top_le_iff_cpt (A := ℂ⟦X⟧) _ _).2 ⟨mem_pull.2 h₀, hM⟩
  choose jf jt hc using exists_cohCharts (Ξ.g v) jM hM'
  obtain ⟨w, hw'⟩ := isUnit_valR (A := ℂ⟦X⟧) _ _ hw (W.w.s (fun _ => j₀, jM))
  have hτ := Ξ.τ_eq v jL jM j₀ hjL hw
  have hI : (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = Ideal.span {PowerSeries.X} :=
    Ideal.map_id _
  have hx := Ξ.x_fm v
  rw [hI, ← hw'] at hτ
  rw [hI] at hx
  let i : Λ.A.X → W.P.D.toPre.X := fun mu => W.e (Λ.ε (α + j • mu))
  have hi : Function.Injective i := fun mu mu' h =>
    smul_right_injective Λ.A.X (Int.natCast_ne_zero.2 (NeZero.ne j)) ((natCast_zsmul mu j).trans
      ((add_left_cancel (Λ.ε.injective (W.e.injective h))).trans (natCast_zsmul mu' j).symm))
  let h : W.P.D.toPre.X → ℂ⟦X⟧ := fun x => w.val ^ j * (famVal (Ξ.g v) (f x) (jf x) * coordVal (Ξ.g v) x (jt x))
  have h₁ : ∀ mu, h (i mu) = PowerSeries.X ^ ((m : ℤ) + Λ.A.exponent j α mu).toNat *
      PowerSeries.C (Λ.A.term j α th mu v * Λ.u.fr j₀ v.2 ^ j) := fun mu => by
    obtain ⟨t, e₁, e₂⟩ := comp mu
    have := GlobalTheory.ConstTerm.main hL hL₂ E H D l Xo c O β Y b a χ W Λ Ξ j (α + j • mu) t (f (i mu)) _
      (fun Z _ _ p κ jf j₀ hp hi => by
        rw [show f (i mu) = _ from e₁]
        exact valR_smul_pullB hW j _ t _ Z p κ jf j₀ hp hi) v jM j₀ _ _ (hc (i mu)) hw
    rw [← hw', e₂] at this
    refine this.trans (congrArg _ (congrArg _ ?_))
    rw [AnArc.term]; ring
  have h₂ : ∀ x, (∀ mu, i mu ≠ x) → h x = 0 := fun x hx => by
    have e₁ : f x = 0 := hf.2 x fun y e => hx (Λ.ε.symm (W.e.symm y)) (by
      rw [← e]
      show W.e (Λ.ε _) = _
      rw [map_add, map_add, map_nsmul, map_nsmul, Λ.ε.apply_symm_apply, W.e.apply_symm_apply])
    have e₂ : famVal (Ξ.g v) (f x) (jf x) = 0 := by
      rw [e₁]
      exact (dif_pos (hc x).1).trans ((congrArg _ (map_zero _)).trans (map_zero _))
    show _ * (_ * _) = _
    rw [e₂, zero_mul, mul_zero]
  beta_reduce
  rw [← algebraMap_mk_eq Λ.A j α th v hpos, ← map_pow, ← map_mul]
  refine congrArg _ ((Units.mul_right_inj (w ^ j)).1 (eq_of_forall_mk_eq (Ideal.span {PowerSeries.X}) fun e => ?_))
  have := isLocalRing_quotient_pow (ne_top_of_isHausdorff (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)})) e
  obtain ⟨F, hF⟩ := map_secVal_eq W.P.U.toUnifPre (hE e)
  obtain ⟨F', hF', hd⟩ := exists_sum_sub_mem hi h₁ h₂ (L := fun k => Λ.A.level j α ((k : ℤ) - m)) (fun k mu => by
    have := hpos mu
    rw [Λ.A.mem_level]
    omega) (e + 1) F
  have H := (hF _ _ _ _ _ hx _ (Ideal.Quotient.mk (Ideal.span {PowerSeries.X} ^ (e + 1))) Ideal.mk_ker.ge).2
    F' jL jM jf jt hF' hjL hM' fun x _ => hc x
  rw [map_mul, H, ← map_mul, Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have e₁ : (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m), Λ.A.term j α th mu v * Λ.u.fr j₀ v.2 ^ j) =
      (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m), Λ.A.term j α th mu v) *
        PowerSeries.C (Λ.u.fr j₀ v.2) ^ j := by
    ext k
    rw [← map_pow, PowerSeries.coeff_mul_C, PowerSeries.coeff_mk, PowerSeries.coeff_mk, Finset.sum_mul]
  rw [e₁, show ∑ x ∈ F', h x = w.val ^ j * ∑ x ∈ F', famVal (Ξ.g v) (f x) (jf x) * coordVal (Ξ.g v) x (jt x) from
    (Finset.mul_sum _ _ _).symm] at hd
  refine (congrArg (_ ∣ ·) ?_).mp (hd.mul_left ((tau W.P.U.toUnifPre (Ideal.span {PowerSeries.X}) (Ξ.x v).left jL jM).val ^ j))
  rw [Units.val_pow_eq_pow_val]
  have := congrArg (· ^ j) hτ
  simp only [mul_pow] at this
  linear_combination (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m), Λ.A.term j α th mu v) * this

end GlobalTheory.ConstThetaSections
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtAnOrthKerIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

theorem gtAn_orth_ker_iff : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (v : Λ.A.La), (∀ v' : Λ.A.La, Λ.ε v'.y = 0 → Λ.A.EF v v' = 0) ↔ (Λ.ε v.y = 0 ∧ ∀ s : ℂ, ∃ x, IsTorusPt (Λ.ex0 (s • Λ.A.P0 v)) x ∧ ∀ v' : Λ.A.La, x (Λ.ε v'.y) = eTwoPi (-(s * Λ.A.EF v v'))) := by
  intro _ _ E _ _ _ H _ D l c O _ β _ _ b a Λ v
  obtain ⟨-, -, htor, hlam⟩ := GlobalTheory.T.analyticDictionaryExp_kernel_iota_torusPoints E H D l c O β b a Λ
  have hε : ∀ x : Λ.A.X, Λ.ε x = 0 ↔ x = 0 := fun x => map_eq_zero_iff _ Λ.ε.injective
  simp only [hε]
  constructor
  · intro h
    refine ⟨((Λ.A.orth_ker_iff v).1 h).1, fun s => ?_⟩
    obtain ⟨h2, h1⟩ := Λ.A.smul_periodMap_of_orthogonal_ker h s
    have hz : s • Λ.A.P0 v = ((s • Λ.A.P0 v).1, 0) := Prod.ext rfl h2
    refine ⟨fun x => eTwoPi ((s • Λ.A.P0 v).1 (Λ.ε.symm x)), ?_, fun v' => ?_⟩
    · have := htor (s • Λ.A.P0 v).1
      rwa [← hz] at this
    · have h3 : Λ.ε.symm (Λ.ε v'.y) = v'.y := Λ.ε.symm_apply_apply _
      simp only [h3, h1]
  · rintro ⟨hv, h⟩
    refine (Λ.A.orth_ker_iff_forall_smul_mem v).2 ⟨hv, fun s => ?_⟩
    obtain ⟨x, hx, -⟩ := h s
    exact hlam _ x hx

end GlobalTheory.ArcPts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyProjCoordsConvergentCoefficientsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_projCoords_convergent_coefficients : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) , AnFin A → Φ.Rational → ∀ (N : ℕ) [NeZero N], 4 ≤ N → Nonempty (Coords Φ N) := by
  first | exact @GlobalTheory.SpanFrame.nonempty_coords | exact GlobalTheory.SpanFrame.nonempty_coords | (intros; apply GlobalTheory.SpanFrame.nonempty_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaSectionsExtendGermRingsAndSpanFibresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSections_extend_germRings_and_span_fibres : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), AnFin A → Φ.Rational → ∀ (j : ℕ) [NeZero j], ∃ T' ≥ Ψ.T, ∀ (w : ℂ) (hw : Ψ.T < w.im), T' < w.im → ∃ σt : A.X → ((Fin A.gB → ℂ) → ℂ) → SecP o.t.PP.L (pullback.fst o.t.G.hom (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT)) j, (∀ α, ∀ th ∈ A.Theta j α, ∀ (q : Over.mk (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT) ⟶ o.t.G) (q' : Over.mk y ⟶ o.t.G) jj, spMap (Γ.R w).val.toRingHom ≫ q.left = q'.left → ⊤ ≤ q.left ⁻¹ᵁ o.t.PP.L.U jj → ((sval (σt α th) (fib q) jj : Γ.R w) : ℂ⸨X⸩) = sval (Φ.sig j α th) (fib q') jj) ∧ ∃ σ₀ : A.X → ((Fin A.gB → ℂ) → ℂ) → SecP o.t.PP.L (pullback.fst o.t.G.hom (Ψ.yw w)) j, (∀ α th (q : Over.mk (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT) ⟶ o.t.G) (q₀ : Over.mk (Ψ.yw w) ⟶ o.t.G) jj, q₀.left = spMap (Γ.ev w).toRingHom ≫ q.left → ⊤ ≤ q₀.left ⁻¹ᵁ o.t.PP.L.U jj → sval (σ₀ α th) (fib q₀) jj = Γ.ev w (sval (σt α th) (fib q) jj)) ∧ (∀ α, ∀ th ∈ A.Theta j α, ∀ v, HasVal (σ₀ α th) (fib (Ψ.pi w v)) (fun jj => Ψ.fr w jj v) (A.Sum j α th w v)) ∧ ∀ s : SecP o.t.PP.L (pullback.fst o.t.G.hom (Ψ.yw w)) j, ∃ (n : ℕ) (r : Fin n → ℂ) (α : Fin n → A.X) (th : Fin n → (Fin A.gB → ℂ) → ℂ), (∀ i, th i ∈ A.Theta j (α i)) ∧ ∀ (q₀ : Over.mk (Ψ.yw w) ⟶ o.t.G) jj, ⊤ ≤ q₀.left ⁻¹ᵁ o.t.PP.L.U jj → sval s (fib q₀) jj = ∑ i, r i * sval (σ₀ (α i) (th i)) (fib q₀) jj := by
  first | exact @GlobalTheory.FibreFrame.sections_extend_and_span | exact GlobalTheory.FibreFrame.sections_extend_and_span | (intros; apply GlobalTheory.FibreFrame.sections_extend_and_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TwoRigidifiedThetaFramesOnFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_rigidified_theta_frames_on_fibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (A : AnArc (𝓞 E)) lin cst (w : ℂ) (y₀ : Sp ℂ ⟶ Xo.X) (π : A.V → (Over.mk y₀ ⟶ Xo.univ.t.G)) fr (g : ℕ) (h : A.V ≃L[ℂ] (Fin g → ℂ)) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Xo.univ.t.G.left)) (ϑ : (Fin g → ℂ) → ℂ) fr', IsFibAt A Xo.univ.t lin cst w y₀ π fr → (∀ v, e (h v) = (π v).left) → IsThetaFrameAt Xo.univ.t.PP y₀ e ϑ fr' → (∃ z, ϑ z ≠ 0) → ∀ th ∈ A.Theta 1 0, (∃ v, A.Sum 1 0 th w v ≠ 0) → ∃ (lam : ℂ) (f : A.V → ℂ), lam ≠ 0 ∧ Differentiable ℂ f ∧ (∀ v, f v ≠ 0) ∧ f 0 = 1 ∧ (∀ v j, ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j (h v) = f v * fr j v) ∧ ∀ v, A.Sum 1 0 th w v = lam * ϑ (h v) * f v := by
  first | exact @GlobalTheory.TwoFrames.two_frames | exact GlobalTheory.TwoFrames.two_frames | (intros; apply GlobalTheory.TwoFrames.two_frames <;> assumption)
end

