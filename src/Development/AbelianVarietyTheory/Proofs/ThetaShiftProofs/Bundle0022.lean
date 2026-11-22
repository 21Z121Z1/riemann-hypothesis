import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueSpecializes
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfForallExistsLsumETwoPi
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLevelPointTangentVectorTransportIff
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.LevelTransport

section Val

variable {X X' Z Z' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {R : Type} [CommRing R]

def wv (w : LB.Iso L' (L.pull F)) (x : Sp R ⟶ X') (j : L.ι) (j' : L'.ι) : R :=
  valR x ((LB.div (L.pull F) L').U (fun _ => j, j')) (w.s (fun _ => j, j')).val

theorem le_div {x : Sp R ⟶ X'} {j : L.ι} {j' : L'.ι} (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ x ⁻¹ᵁ L'.U j') :
    ⊤ ≤ x ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, j') :=
  fun _ hz => ⟨mem_pull.2 (hj hz), hj' hz⟩

theorem isUnit_wv (w : LB.Iso L' (L.pull F)) {x : Sp R ⟶ X'} {j : L.ι} {j' : L'.ι}
    (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ x ⁻¹ᵁ L'.U j') : IsUnit (wv w x j j') :=
  FormalValue.isUnit_valR x _ (le_div hj hj') _

theorem toStkA_wv (w : LB.Iso L' (L.pull F)) {x : Sp R ⟶ X'} {j : L.ι} {j' : L'.ι}
    (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ x ⁻¹ᵁ L'.U j') (z : Sp R) :
    toStkA z (wv w x j j') = (gw w x z j j').val :=
  toStkA_valR x _ z (le_div hj hj') _

def secSub {M : LB X} (a b : M.Sec) : M.Sec where
  f i := a.f i - b.f i
  compat i j := by rw [map_sub, map_sub, a.compat, b.compat, mul_sub]

variable [IsLocalRing R]

theorem exists_chart_pt (hL : L.IsLB) (x : Sp R ⟶ X) : ∃ j, ⊤ ≤ x ⁻¹ᵁ L.U j :=
  Points.exists_le_preimage_of_iSup_eq_top x hL.cover

theorem wv_trans {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) {x : Sp R ⟶ X'} {j k : L.ι} {j' k' : L'.ι}
    (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j) (hk : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U k) (hj' : ⊤ ≤ x ⁻¹ᵁ L'.U j') (hk' : ⊤ ≤ x ⁻¹ᵁ L'.U k') :
    wv w x j j' * valR x (L'.U j' ⊓ L'.U k') (L'.g j' k').val =
      valR (x ≫ F) (L.U j ⊓ L.U k) (L.g j k).val * wv w x k k' := by
  apply toStkA_injective
  have t : cpt R ∈ (⊤ : (Sp R).Opens) := trivial
  rw [map_mul, map_mul, toStkA_wv w hj hj', toStkA_wv w hk hk',
    toStkA_valR x (L'.U j' ⊓ L'.U k') _ (fun _ hz => ⟨hj' hz, hk' hz⟩),
    toStkA_valR (x ≫ F) (L.U j ⊓ L.U k) _ (fun _ hz => ⟨hj hz, hk hz⟩),
    (isGen_iff w).1 hw _ x (cpt R) j k j' k' (hj t) (hk t) (hj' t) (hk' t), ← Units.val_mul, ← Units.val_mul,
    mul_right_comm, inv_mul_cancel_right]

theorem valR_g_self (hL : L.IsLB) {x : Sp R ⟶ X} {j : L.ι} (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valR x (L.U j ⊓ L.U j) (L.g j j).val = 1 := by
  apply toStkA_injective
  rw [toStkA_valR x (L.U j ⊓ L.U j) _ (fun _ hz => ⟨hj hz, hj hz⟩), gm_self hL x _ (hj trivial), map_one, Units.val_one]

def FrmRel (w : LB.Iso L' (L.pull F)) (x : Sp R ⟶ X') (τ : L.ι → R) (τ' : L'.ι → R) : Prop :=
  ∀ j j', ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j → ⊤ ≤ x ⁻¹ᵁ L'.U j' → τ j = wv w x j j' * τ' j'

theorem exists_frm_up {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) {x : Sp R ⟶ X'}
    {τ' : L'.ι → R} (h : IsFrm L' x τ') : ∃ τ, IsFrm L (x ≫ F) τ ∧ FrmRel w x τ τ' := by
  obtain ⟨k', hk'⟩ := exists_chart_pt hL' x
  refine ⟨fun j => wv w x j k' * τ' k', ⟨fun j hj => (isUnit_wv w hj hk').mul (h.1 k' hk'), fun j k hjk => ?_⟩,
    fun j j' hj hj' => ?_⟩
  · have e := wv_trans hw (fun _ hz => (hjk hz).1) (fun _ hz => (hjk hz).2) hk' hk'
    rw [valR_g_self hL' hk', _root_.mul_one] at e
    simp only [e, _root_.mul_assoc]
  · have e := wv_trans hw hj hj hj' hk'
    rw [valR_g_self hL hj, _root_.one_mul] at e
    rw [h.2 j' k' (fun _ hz => ⟨hj' hz, hk' hz⟩), ← _root_.mul_assoc, e]

theorem exists_frm_down {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) {x : Sp R ⟶ X'}
    {τ : L.ι → R} (h : IsFrm L (x ≫ F) τ) : ∃ τ', IsFrm L' x τ' ∧ FrmRel w x τ τ' := by
  obtain ⟨k, hk⟩ := exists_chart_pt hL (x ≫ F)
  have hi : ∀ j', ⊤ ≤ x ⁻¹ᵁ L'.U j' → wv w x k j' * (Ring.inverse (wv w x k j') * τ k) = τ k := fun j' hj' => by
    rw [← _root_.mul_assoc, Ring.mul_inverse_cancel _ (isUnit_wv w hk hj'), _root_.one_mul]
  refine ⟨fun j' => Ring.inverse (wv w x k j') * τ k, ⟨fun j' hj' => ?_, fun j' k' hjk => ?_⟩,
    fun j j' hj hj' => ?_⟩
  · exact isUnit_of_mul_isUnit_right ((hi j' hj').symm ▸ h.1 k hk)
  · have hj' : ⊤ ≤ x ⁻¹ᵁ L'.U j' := fun _ hz => (hjk hz).1
    have hk' : ⊤ ≤ x ⁻¹ᵁ L'.U k' := fun _ hz => (hjk hz).2
    have e := wv_trans hw hk hk hj' hk'
    rw [valR_g_self hL hk, _root_.one_mul] at e
    refine (isUnit_wv w hk hj').mul_left_cancel ?_
    beta_reduce
    rw [hi j' hj', ← _root_.mul_assoc, e, hi k' hk']
  · have e := wv_trans hw hj hk hj' hj'
    rw [valR_g_self hL' hj', _root_.mul_one] at e
    beta_reduce
    rw [e, _root_.mul_assoc, hi j' hj']
    exact h.2 j k (fun _ hz => ⟨hj hz, hk hz⟩)

variable {w : LB.Iso L' (L.pull F)} {p : Z ⟶ X} {p' : Z' ⟶ X'} {h : Z' ⟶ Z} {k : ℕ} {a : SecP L' p' k} {t : SecP L p k}

theorem sval_through (hψ : p' ≫ F = h ≫ p)
    (H : ConstFam.SecThrough w (fun _ : Fin 1 => p') (fun _ => p) (fun _ => (k : ℤ)) a t h) (r : Sp R ⟶ Z')
    {j : L.ι} {j' : L'.ι} (hj : ⊤ ≤ ((r ≫ p') ≫ F) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ (r ≫ p') ⁻¹ᵁ L'.U j') :
    ArcPts.sval t (r ≫ h) j = wv w (r ≫ p') j j' ^ k * ArcPts.sval a r j' := by
  apply toStkA_injective
  have hj₂ : ⊤ ≤ ((r ≫ h) ≫ p) ⁻¹ᵁ L.U j := by rwa [Category.assoc, ← hψ, ← Category.assoc]
  have m₁ : ⊤ ≤ (r ≫ h) ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j) :=
    fun _ hz => Set.mem_iInter.2 fun _ => hj₂ hz
  have m₂ : ⊤ ≤ r ⁻¹ᵁ LB.wchart L' (fun _ : Fin 1 => p') (fun _ => j') :=
    fun _ hz => Set.mem_iInter.2 fun _ => hj' hz
  rw [map_mul, map_pow, toStkA_wv w hj hj']
  refine (FormalValue.toStkA_valR_eq_gs _ _ _ m₁ _).trans
    ((H _ r (cpt R) (fun _ => j) (fun _ => j') (fun _ => hj trivial) (fun _ => hj' trivial)).trans
      (congrArg₂ (· * ·) ?_ (FormalValue.toStkA_valR_eq_gs _ _ _ m₂ _).symm))
  simp

theorem hasVal_iff (hL : L.IsLB) (hL' : L'.IsLB) (hψ : p' ≫ F = h ≫ p)
    (H : ConstFam.SecThrough w (fun _ : Fin 1 => p') (fun _ => p) (fun _ => (k : ℤ)) a t h) (r : Sp R ⟶ Z')
    {τ : L.ι → R} {τ' : L'.ι → R} (hτ : FrmRel w (r ≫ p') τ τ') (c : R) :
    ArcPts.HasVal a r τ' c ↔ ArcPts.HasVal t (r ≫ h) τ c := by
  have e : (r ≫ h) ≫ p = (r ≫ p') ≫ F := by rw [Category.assoc, ← hψ, Category.assoc]
  constructor
  · intro ha j hj
    rw [e] at hj
    obtain ⟨j', hj'⟩ := exists_chart_pt hL' (r ≫ p')
    rw [sval_through hψ H r hj hj', ha j' hj', hτ j j' hj hj']
    ring
  · intro ht j' hj'
    obtain ⟨j, hj⟩ := exists_chart_pt hL ((r ≫ p') ≫ F)
    refine ((isUnit_wv w hj hj').pow k).mul_left_cancel ?_
    rw [← sval_through hψ H r hj hj', ht j (e ▸ hj), hτ j j' hj hj']
    ring

omit [IsLocalRing R] in
theorem hasVal_secSub {a b : SecP L p k} {r : Sp R ⟶ Z} {τ : L.ι → R} {c : R} (ha : ArcPts.HasVal a r τ c)
    (hb : ArcPts.HasVal b r τ c) : ArcPts.HasVal (secSub a b) r τ 0 := by
  intro j hj
  have hm : ⊤ ≤ r ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j) := fun _ hz => Set.mem_iInter.2 fun _ => hj hz
  have e₁ := (Points.valR_eq _ _ hm _).symm.trans (ha j hj)
  have e₂ := (Points.valR_eq _ _ hm _).symm.trans (hb j hj)
  rw [zero_mul]
  exact (Points.valR_eq _ _ hm _).trans ((map_sub _ _ _).trans (sub_eq_zero.2 (e₁.trans e₂.symm)))

end Val

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {S S' : Scheme.{0}}
  {A : AnArc (𝓞 E)} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} {m : SABMap t' t f}
  {w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)} {y' : Sp ℂ⸨X⸩ ⟶ S'} {y : Sp ℂ⸨X⸩ ⟶ S}
  {Φ' : GenPts A t' y'} {Φ : GenPts A t y} {h : pullback t'.G.hom y' ⟶ pullback t.G.hom y}

omit [StarRing (𝓞 E)] in
theorem fib_comp (h₁ : pullback.fst _ _ ≫ m.φ = h ≫ pullback.fst _ _) (h₂ : h ≫ pullback.snd _ _ = pullback.snd _ _)
    {p' : Over.mk y' ⟶ t'.G} {p : Over.mk y ⟶ t.G} (e : p'.left ≫ m.φ = p.left) : fib p' ≫ h = fib p := by
  apply pullback.hom_ext
  · rw [Category.assoc, ← h₁, fib, fib, pullback.lift_fst_assoc, pullback.lift_fst, e]
  · rw [Category.assoc, h₂, fib, fib, pullback.lift_snd, pullback.lift_snd]

theorem fib_fst {R : Type} [CommRing R] {G : Over S} {y : Sp R ⟶ S} (x : Over.mk y ⟶ G) :
    fib x ≫ pullback.fst _ _ = x.left := pullback.lift_fst _ _ _

theorem sig_through (hw : w.IsGen) (hR : GenPts.Rel m w Φ' Φ) (h₁ : pullback.fst _ _ ≫ m.φ = h ≫ pullback.fst _ _)
    (h₂ : h ≫ pullback.snd _ _ = pullback.snd _ _) (k : ℕ) [NeZero k] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ)
    (hth : th ∈ A.Theta k α) :
    ConstFam.SecThrough w (fun _ : Fin 1 => pullback.fst t'.G.hom y') (fun _ => pullback.fst t.G.hom y)
      (fun _ => (k : ℤ)) (Φ'.sig k α th) (Φ.sig k α th) h := by
  obtain ⟨a, ha⟩ := ConstFam.exists_secThrough (φ' := fun _ : Fin 1 => pullback.fst t'.G.hom y')
    hw t.PP.isLB t'.PP.isLB (fun _ => h₁) (Φ.sig k α th)
  have hv : ∀ v, ArcPts.HasVal (m := k) a (fib (Φ'.x v)) (Φ'.τ v) (A.FSum k α th v) := fun v => by
    refine (hasVal_iff t.PP.isLB t'.PP.isLB h₁ ha _ (τ := Φ.τ v) ?_ _).2 ?_
    · rw [fib_fst]
      exact fun j j' hj hj' => (hR.2 v).2 j j' (le_div hj hj')
    · rw [fib_comp h₁ h₂ (hR.2 v).1]
      exact Φ.val k α th hth v
  have e : a.f = (Φ'.sig k α th).f := funext fun i => sub_eq_zero.1
    (Φ'.sep k (secSub a (Φ'.sig k α th)) (fun v => hasVal_secSub (hv v) (Φ'.val k α th hth v)) i)
  intro Z r z p q hp hq
  rw [← e]
  exact ha Z r z p q hp hq

theorem levelPt_iff (hw : w.IsGen) (hR : GenPts.Rel m w Φ' Φ) (h₁ : pullback.fst _ _ ≫ m.φ = h ≫ pullback.fst _ _)
    (h₂ : h ≫ pullback.snd _ _ = pullback.snd _ _) (k : ℕ) [NeZero k] (p' : Over.mk y' ⟶ t'.G)
    (p : Over.mk y ⟶ t.G) (la : A.La) (e : p'.left ≫ m.φ = p.left) : Φ'.LevelPt k p' la ↔ Φ.LevelPt k p la := by
  obtain ⟨π, hπ⟩ := LiePull.exists_pushEquiv m.cart (Over.mk y') y hR.1.symm
  obtain rfl : π p' = p := Over.OverMorphism.ext ((hπ p').trans e)
  have hx : ∀ z, (Φ'.x z * p').left ≫ m.φ = (Φ.x z * π p').left := fun z => by
    have : π (Φ'.x z) = Φ.x z := Over.OverMorphism.ext ((hπ _).trans (hR.2 z).1)
    rw [← this, ← map_mul, hπ]
  have key : ∀ (α α' : A.X), ∀ th ∈ A.Theta k α, ∀ th' ∈ A.Theta k α', ∀ (z : A.V) (F F' : ℂ⸨X⸩) j j',
      ⊤ ≤ (Φ.x z * π p').left ⁻¹ᵁ t.PP.L.U j → ⊤ ≤ (Φ'.x z * p').left ⁻¹ᵁ t'.PP.L.U j' →
      (ArcPts.sval (Φ'.sig k α th) (fib (Φ'.x z * p')) j' * F' =
          ArcPts.sval (Φ'.sig k α' th') (fib (Φ'.x z * p')) j' * F ↔
        ArcPts.sval (Φ.sig k α th) (fib (Φ.x z * π p')) j * F' =
          ArcPts.sval (Φ.sig k α' th') (fib (Φ.x z * π p')) j * F) := by
    intro α α' th hth th' hth' z F F' j j' hj hj'
    rw [← hx, ← fib_fst] at hj
    rw [← fib_fst] at hj'
    rw [← fib_comp h₁ h₂ (hx z), sval_through h₁ (sig_through hw hR h₁ h₂ k α th hth) _ hj hj',
      sval_through h₁ (sig_through hw hR h₁ h₂ k α' th' hth') _ hj hj', _root_.mul_assoc, _root_.mul_assoc]
    exact ((isUnit_wv w hj hj').pow k).mul_right_inj.symm
  refine and_congr (by rw [← map_pow, MulEquiv.map_eq_one_iff]) (and_congr Iff.rfl ⟨?_, ?_⟩)
  · intro H α α' th hth th' hth' z F F' j hF hF' hj
    obtain ⟨j', hj'⟩ := exists_chart_pt t'.PP.isLB (R := ℂ⸨X⸩) (Φ'.x z * p').left
    exact (key α α' th hth th' hth' z F F' j j' hj hj').1 (H α α' th hth th' hth' z F F' j' hF hF' hj')
  · intro H α α' th hth th' hth' z F F' j' hF hF' hj'
    obtain ⟨j, hj⟩ := exists_chart_pt t.PP.isLB (R := ℂ⸨X⸩) (Φ.x z * π p').left
    exact (key α α' th hth th' hth' z F F' j j' hj hj').2 (H α α' th hth th' hth' z F F' j hF hF' hj)

theorem isTan_iff (hw : w.IsGen) (hR : GenPts.Rel m w Φ' Φ) (h₁ : pullback.fst _ _ ≫ m.φ = h ≫ pullback.fst _ _)
    (h₂ : h ≫ pullback.snd _ _ = pullback.snd _ _) (z₀ : A.V) (ν' : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t'.G.hom y') :
    Φ'.IsTan z₀ ν' ↔ Φ.IsTan z₀ (ν' ≫ h) := by
  have inj : ∀ {T : Scheme.{0}} (a b : T ⟶ pullback t'.G.hom y'), a ≫ h = b ≫ h → a = b := fun a b e => by
    have e₂ : a ≫ pullback.snd _ _ = b ≫ pullback.snd _ _ := by rw [← h₂, reassoc_of% e]
    refine pullback.hom_ext (m.cart.1.hom_ext ?_ ?_) e₂
    · rw [Category.assoc, Category.assoc, h₁, reassoc_of% e]
    · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% e₂]
  have e : (ν' ≫ h) ≫ pullback.fst _ _ = (ν' ≫ pullback.fst _ _) ≫ m.φ := by
    rw [Category.assoc, Category.assoc, h₁]
  refine and_congr (by rw [Category.assoc, h₂]) (and_congr ?_ ⟨?_, ?_⟩)
  · rw [← fib_comp h₁ h₂ (hR.2 0).1, ← Category.assoc]
    exact ⟨fun c => by rw [c], inj _ _⟩
  · rintro ⟨τ', hτ', H⟩
    obtain ⟨τ, hτ, hr⟩ := exists_frm_up hw t.PP.isLB t'.PP.isLB hτ'
    exact ⟨τ, e ▸ hτ, fun j _ α th hth F hF =>
      (hasVal_iff t.PP.isLB t'.PP.isLB h₁ (sig_through hw hR h₁ h₂ j α th hth) ν' hr _).1 (H j α th hth F hF)⟩
  · rintro ⟨τ, hτ, H⟩
    rw [e] at hτ
    obtain ⟨τ', hτ', hr⟩ := exists_frm_down hw t.PP.isLB t'.PP.isLB hτ
    exact ⟨τ', hτ', fun j _ α th hth F hF =>
      (hasVal_iff t.PP.isLB t'.PP.isLB h₁ (sig_through hw hR h₁ h₂ j α th hth) ν' hr _).2 (H j α th hth F hF)⟩

end Main

theorem levelPt_isTan_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S S' : Scheme.{0}) (A : AnArc (𝓞 E)) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) (y' : Sp ℂ⸨X⸩ ⟶ S') (y : Sp ℂ⸨X⸩ ⟶ S) (Φ' : GenPts A t' y') (Φ : GenPts A t y), w.IsGen → GenPts.Rel m w Φ' Φ → (∀ (k : ℕ) [NeZero k] (p' : Over.mk y' ⟶ t'.G) (p : Over.mk y ⟶ t.G) la, p'.left ≫ m.φ = p.left → (Φ'.LevelPt k p' la ↔ Φ.LevelPt k p la)) ∧ ∀ z₀ (ν' : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t'.G.hom y') (ν : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t.G.hom y), ν' ≫ pullback.fst _ _ ≫ m.φ = ν ≫ pullback.fst _ _ → ν' ≫ pullback.snd _ _ = ν ≫ pullback.snd _ _ → (Φ'.IsTan z₀ ν' ↔ Φ.IsTan z₀ ν) := by
  intro E _ _ _ H _ S S' A t t' f m w y' y Φ' Φ hw hR
  let h : pullback t'.G.hom y' ⟶ pullback t.G.hom y := pullback.lift (pullback.fst _ _ ≫ m.φ) (pullback.snd _ _) (by
    rw [Category.assoc, m.cart.1.w, pullback.condition_assoc, hR.1])
  have h₁ : pullback.fst _ _ ≫ m.φ = h ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
  have h₂ : h ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  refine ⟨fun k _ p' p la e => levelPt_iff hw hR h₁ h₂ k p' p la e, fun z₀ ν' ν e₁ e₂ => ?_⟩
  obtain rfl : ν' ≫ h = ν := pullback.hom_ext (by rw [Category.assoc, ← h₁, e₁]) (by rw [Category.assoc, h₂, e₂])
  exact isTan_iff hw hR h₁ h₂ z₀ ν'

end GlobalTheory.LevelTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CardQkOfTateIsoQ
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section
namespace GlobalTheory.ArcPts
open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem card_qk_pre (hL : Out.Laws) (hL2 : Out.Laws2) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (D₀ : Out.DegPre R) (hB : D₀.TauBimult) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
    (k : ℕ) (hk : (k : F) ≠ 0) :
    Nat.card (Quot (Out.QkPt.Equiv D₀ F (k := k))) = k ^ (2 * (D₀.rank + D₀.P.g)) := by
  have hk0 : k ≠ 0 := by rintro rfl; exact hk Nat.cast_zero
  have h₁ := (GlobalTheory.GtCount.card_gtTors hL hL2 R D₀ F k hk).1
  simp only [GlobalTheory.GtCount.gtTors_iff] at h₁
  rw [GlobalTheory.UT.card_qk_eq_mul hB hk0 fun y => exists_nsmul_eq hL.mulN (Or.inl inferInstance) hk0 _, h₁, ← pow_add]
  congr 1
  ring

theorem card_qk_of_tateIsoQ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {R : Type} [CommRing R] [IsDomain R] {D₀ : Out.DegPre R} [Module (𝓞 E) D₀.X]
    {oa : letI := H.starRing; D₀.OAct (𝓞 E)} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (hB : D₀.TauBimult) (I : TateIsoQ D D₀ oa F) (k : ℕ) (hk : 0 < k) :
    Nat.card (Quot (Out.QkPt.Equiv D₀ F (k := k))) = k ^ Module.finrank ℤ D.La := by
  have := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have := datum_free_int D
  let K : AddSubgroup D.La := (nsmulAddMonoidHom k : D.La →+ D.La).range
  have hK : Nat.card (D.La ⧸ K) = k ^ Module.finrank ℤ D.La := AddSubgroup.index_range_nsmul D.La k
  have hE := equiv_equivalence (D := D₀) (F := F) (k := k) hB
  let f : D.La ⧸ K → Quot (Out.QkPt.Equiv D₀ F (k := k)) := fun x => Quot.mk _ (I.ev k x.out)
  rw [← hK]
  refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
  · intro x x' h
    obtain ⟨e, he⟩ := (I.ker k hk _ _).1 (hE.symm (hE.eqvGen_iff.1 (Quot.eqvGen_exact h)))
    rw [← QuotientAddGroup.out_eq' x, ← QuotientAddGroup.out_eq' x', QuotientAddGroup.eq]
    exact ⟨e, by rw [he, neg_add_cancel_left]; rfl⟩
  · rintro ⟨p⟩
    obtain ⟨v, hv⟩ := I.onto k hk p
    obtain ⟨e, he⟩ : -v + (QuotientAddGroup.mk v : D.La ⧸ K).out ∈ K := by
      rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
    refine ⟨QuotientAddGroup.mk v, Quot.sound (hE.trans ((I.ker k hk _ _).2 ⟨e, ?_⟩) hv)⟩
    rw [show k • e = _ from he, add_neg_cancel_left]

theorem finrank_V_eq : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → (∃ r z : O, ((β r : c.F) : ℂ) = H.rt0 ∧ ((β z : c.F) : ℂ) = zeta l.A) → Module.finrank ℂ Λ.A.V = g := by
  intro hL hL2 E _ _ _ H _ D l c O _ β _ _ b a Λ g ty hty ⟨r, z, hr, hz⟩
  obtain ⟨-, I, -⟩ := a.geom ℂ r z hr hz _ rfl
  have h₁ := card_qk_pre hL hL2 a.D₀ a.bimult ℂ 2 (by norm_num)
  rw [card_qk_of_tateIsoQ a.bimult I 2 two_pos, datum_finrank_int,
    ← (GlobalTheory.PeriodExists.period_of_isTypeFn H D g ty hty).1] at h₁
  have h₂ := Nat.pow_right_injective le_rfl h₁
  have h₃ : Module.finrank ℤ Λ.A.X = a.D₀.rank := (Λ.ε.toAddEquiv.toIntLinearEquiv).finrank_eq
  rw [Λ.A.finrank_V, h₃, Λ.gB_eq]
  omega

end GlobalTheory.ArcPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoordsDetermineFamily
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.CoordFamily

open Filter Topology GlobalTheory.Specialise GlobalTheory.AmpleSpan GlobalTheory.HolHom

variable {X Y : Scheme.{0}} {f : X ⟶ Y} {H : LB X} {I : Type} {t : I → LB.Sec H}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {x : V → (Sp ℂ ⟶ X)} {cf : I → V → ℂ}

theorem eq_of_proportional (ht : EmbedsBy f t) {p p' : Sp ℂ ⟶ X} (hf : p ≫ f = p' ≫ f) {c c' : I → ℂ}
    (h : HasCoords p t c) (h' : HasCoords p' t c') {ρ : ℂ} (e : ∀ i, c' i = ρ * c i) : p = p' := by
  obtain ⟨m, hm⟩ := h'.exists_isUnit ht.1
  have hρ : IsUnit ρ := isUnit_of_mul_isUnit_left (e m ▸ hm)
  have h₁ := h.mul_unit hρ
  have e' : (fun l => c l * ρ) = c' := funext fun l => by rw [e, mul_comm]
  rw [e'] at h₁
  exact h₁.ext ht hf h' hm

theorem holAt_of_coords (ht : EmbedsBy f t) {y : Sp ℂ ⟶ Y} (hy : ∀ v, x v ≫ f = y)
    (hc : ∀ v, HasCoords (x v) t fun i => cf i v) {z : V} (hd : ∀ i, DifferentiableAt ℂ (cf i) z) : HolAt x z := by
  obtain ⟨m, hm⟩ := (hc z).exists_isUnit ht.1
  obtain ⟨hD, ρ, hρ, hsurj⟩ := ht.2 m
  have hne : ∀ᶠ v in 𝓝 z, cf m v ≠ 0 := (hd m).continuousAt.eventually_ne hm.ne_zero
  have hev : ∀ᶠ v in 𝓝 z, ⊤ ≤ x v ⁻¹ᵁ Out.nonzeroLocus (t m) :=
    hne.mono fun v hv => (hc v).le_nonzeroLocus hv.isUnit
  refine holAt_of_affine hD hev.self_of_nhds hev fun g => ?_
  obtain ⟨q, rfl⟩ := hsurj g
  induction q using MvPolynomial.induction_on with
  | C a =>
    refine (differentiableAt_const (valR y ⊤ a)).congr_of_eventuallyEq (hev.mono fun v hv => ?_)
    simp only [MvPolynomial.eval₂Hom_C, valAt'_eq_valR]
    exact (HolHom.valR_appLE (x v) f ⊤ _ le_top a hv).trans (by rw [hy])
  | add p q hp hq =>
    refine (hp.add hq).congr_of_eventuallyEq (hev.mono fun v hv => ?_)
    simp only [valAt'_eq_valR, HolHom.valR_eq _ _ hv, map_add, Pi.add_apply]
  | mul_X p l hp =>
    refine (hp.mul ((hd l).fun_mul ((hd m).fun_inv hm.ne_zero))).congr_of_eventuallyEq
      ((hev.and hne).mono fun v hv => ?_)
    have e := (hc v).valR_ratio hv.1 (hρ l)
    have e' : valR (x v) _ (ρ l) = cf l v * (cf m v)⁻¹ := by
      rw [← e, mul_inv_cancel_right₀ hv.2]
    simp only [valAt'_eq_valR, map_mul, MvPolynomial.eval₂Hom_X', Pi.mul_apply]
    rw [← e']
    simp only [HolHom.valR_eq _ _ hv.1, map_mul]

theorem hasCoords_deriv (hcov : ⨆ l, Out.nonzeroLocus (t l) = ⊤) (hc : ∀ v, HasCoords (x v) t fun i => cf i v)
    {z w : V} (hx : HolAt x z) (hd : ∀ i, DifferentiableAt ℂ (cf i) z) {ν : Sp (DualNumber ℂ) ⟶ X}
    (hν : IsDerivAt x z w ν) :
    HasCoords ν t fun i => TrivSqZeroExt.inl (cf i z) + TrivSqZeroExt.inr (fderiv ℂ (cf i) z w) := by
  obtain ⟨m, hm⟩ := (hc z).exists_isUnit hcov
  choose ρ hρ using fun l => exists_isRatio (t l) (t m)
  have hz := (hc z).le_nonzeroLocus hm
  have hν' := (le_preimage_dual_iff hν.1 _).2 hz
  have hu : IsUnit (TrivSqZeroExt.inl (cf m z) + TrivSqZeroExt.inr (fderiv ℂ (cf m) z w) : DualNumber ℂ) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by simpa using hm)
  have h₁ := (hasCoords_ratio hν' hρ).mul_unit hu
  convert h₁ using 2 with l
  have hev : cf l =ᶠ[𝓝 z] fun v => valAt' (x v) _ (ρ l) * cf m v :=
    (hx _ hz).1.mono fun v hv => ((hc v).valR_ratio hv (hρ l)).symm
  have h0 := hev.self_of_nhds
  beta_reduce at h0
  rw [hev.fderiv_eq, h0, fderiv_fun_mul ((hx _ hz).2 _) (hd m)]
  ext
  · simp [fst_valR hν.1 hz]
  · simp [fst_valR hν.1 hz, hν.2 _ hz, mul_comm]

theorem isDerivAt_of_coords (ht : EmbedsBy f t) {y : Sp ℂ ⟶ Y} (hy : ∀ v, x v ≫ f = y)
    (hc : ∀ v, HasCoords (x v) t fun i => cf i v) {z w : V} (hd : ∀ i, DifferentiableAt ℂ (cf i) z)
    {ν : Sp (DualNumber ℂ) ⟶ X} (hb : ν ≫ f = constVec y)
    (hν : HasCoords ν t fun i => TrivSqZeroExt.inl (cf i z) + TrivSqZeroExt.inr (fderiv ℂ (cf i) z w)) :
    IsDerivAt x z w ν := by
  have hx := holAt_of_coords ht hy hc hd
  obtain ⟨ν', hν'⟩ := hx.exists_isDerivAt w
  have h1 := hν'.comp f
  have h2 : (fun v => x v ≫ f) = fun _ => y := funext hy
  have h3 : ν' ≫ f = constVec y := (h2 ▸ h1).unique (isDerivAt_const y z w)
  rw [hν.ext_of_isLocalRing ht (hb.trans h3.symm) (hasCoords_deriv ht.1 hc hx hd hν')]
  exact hν'

theorem hasCoords_powOver {S : Scheme.{0}} {G : Over S} {L : LB G.left} (hL : L.IsLB) {U : S.Opens} {N : ℕ}
    {b : I → LB.Sec (Out.powOver G L U N)} {A : Type} [CommRing A] [IsLocalRing A]
    {p : Sp A ⟶ (G.hom ⁻¹ᵁ U).toScheme} {c : I → A}
    (h : ∀ j, ⊤ ≤ (p ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → ∃ u : Aˣ,
      ∀ i, valR p ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = c i * u) : HasCoords p b c := by
  obtain ⟨j, hj⟩ := Points.exists_le_preimage_of_iSup_eq_top (p ≫ (G.hom ⁻¹ᵁ U).ι) hL.cover
  exact ⟨fun _ => j, fun s hs => Set.mem_iInter.2 fun _ => hj hs, h j hj⟩

end GlobalTheory.CoordFamily

namespace GlobalTheory

open Specialise HolHom CoordFamily in

theorem coords_determine_family : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (U : S.Opens) (N n : ℕ) (b : Fin n → LB.Sec (Out.powOver G L U N)) (y : Sp ℂ ⟶ S) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (x : V → (Sp ℂ ⟶ (G.hom ⁻¹ᵁ U).toScheme)) (cf : Fin n → V → ℂ), L.IsLB → IsAffineOpen U → AmpleSpan.EmbedsBy (G.hom ∣_ U) b → (∀ v, x v ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = y) → (∀ v j, ⊤ ≤ (x v ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → ∃ u : ℂ, u ≠ 0 ∧ ∀ i, valR (x v) ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = cf i v * u) → (∀ v v' (ρ : ℂ), (∀ i, cf i v' = ρ * cf i v) → x v' = x v) ∧ ((∀ i, Differentiable ℂ (cf i)) → IsHolTo Set.univ (fun v => x v ≫ (G.hom ⁻¹ᵁ U).ι) ∧ ∀ (z₀ : V) (ν : Sp (DualNumber ℂ) ⟶ (G.hom ⁻¹ᵁ U).toScheme), ν ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y → (∀ j, ⊤ ≤ (ν ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → ∃ u : (DualNumber ℂ)ˣ, ∀ i, valR ν ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = (TrivSqZeroExt.inl (cf i 0) + TrivSqZeroExt.inr (fderiv ℂ (cf i) 0 z₀)) * (u : DualNumber ℂ)) → ∀ (W : G.left.Opens) (f : Γ(G.left, W)), spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ ν = x 0 ∧ (⊤ ≤ (x 0 ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ W → TrivSqZeroExt.snd (valR (ν ≫ (G.hom ⁻¹ᵁ U).ι) W f) = fderiv ℂ (fun v => valAt' (x v ≫ (G.hom ⁻¹ᵁ U).ι) W f) 0 z₀)) := by
  intro S G _ L U N n b y V _ _ x cf hL _ hb hy hc
  have hc' : ∀ v, HasCoords (x v) b fun i => cf i v := fun v => hasCoords_powOver hL fun j hj => by
    obtain ⟨u, hu, e⟩ := hc v j hj
    exact ⟨Units.mk0 u hu, e⟩
  have hi : (G.hom ∣_ U) ≫ U.ι = (G.hom ⁻¹ᵁ U).ι ≫ G.hom := morphismRestrict_ι _ _
  have hy' : ∀ v, x v ≫ (G.hom ∣_ U) = x 0 ≫ (G.hom ∣_ U) := fun v => by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hi, hy, hy]
  refine ⟨fun v v' ρ e => (eq_of_proportional hb ((hy' v).trans (hy' v').symm) (hc' v) (hc' v') e).symm,
    fun hd => ⟨isHolTo_of_holAt isOpen_univ fun z _ => (holAt_of_coords hb hy' hc' fun i => hd i z).comp _,
      fun z₀ ν hν hνc W f => ?_⟩⟩
  have h := isDerivAt_of_coords (w := z₀) hb hy' hc' (fun i => hd i 0) (ν := ν)
    (by rw [← cancel_mono U.ι, Category.assoc, Category.assoc, Category.assoc, hi, hν, hy])
    (hasCoords_powOver hL hνc)
  exact ⟨h.1, fun hW => (h.comp (G.hom ⁻¹ᵁ U).ι).2 W hW f⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCoeffMemSubfield
section
noncomputable section

namespace GlobalTheory.ArcPts

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory Filter
open scoped LaurentSeries PowerSeries

theorem exists_coeff_mem_subfield {k L V ι : Type*} [Field k] [Field L] [Algebra k L] [Fintype ι]
    (K : IntermediateField k L) (r : ι → L) (g : ι → V → L) (f : V → L) (hg : ∀ i v, g i v ∈ K)
    (hf : ∀ v, f v ∈ K) (h : ∀ v, f v = ∑ i, r i * g i v) :
    ∃ s : ι → L, (∀ i, s i ∈ K) ∧ ∀ v, f v = ∑ i, s i * g i v := by
  obtain ⟨π, hπ⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap K L).injective)
  refine ⟨fun i => π (r i), fun i => (π (r i)).2, fun v => ?_⟩
  have h1 : π (f v) = ⟨f v, hf v⟩ := LinearMap.congr_fun hπ ⟨f v, hf v⟩
  have h2 : π (f v) = ∑ i, π (r i) * ⟨g i v, hg i v⟩ := by
    rw [h v, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : r i * g i v = (⟨g i v, hg i v⟩ : K) • r i := by
      rw [mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have h3 := congrArg (fun x : K => (x : L)) (h1.symm.trans h2)
  simpa using h3

theorem exists_isComb_halfRing : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), AnFin A →
    ∀ (j : ℕ) [NeZero j] (f : A.V → ℂ⸨X⸩), IsComb A j Set.univ f → (∀ v, f v ∈ Conv.convLaurent) →
    ∃ T : ℝ, IsComb A j (Conv.halfRing T) f ∧ ∀ v, f v ∈ Conv.halfRing T := by
  rintro O _ _ A - j _ f ⟨n, r, α, th, h1, h2⟩ hf
  obtain ⟨T₀, h₀⟩ := A.exists_isConvLine
  have hm : ∀ i v, A.FSum j (α i) (th i) v ∈ Conv.halfRing T₀ := fun i v _ hw =>
    (AnArc.hasSum_coeff_FSum h₀ (h1 i).2 hw v).summable
  obtain ⟨s, hs, hfs⟩ := exists_coeff_mem_subfield Conv.convLaurent r (fun i v => A.FSum j (α i) (th i) v) f
    (fun i v => Conv.halfRing_le_convLaurent T₀ (hm i v)) hf h2
  obtain ⟨T, hT, hT₀⟩ := ((eventually_all.2 fun i => Conv.eventually_mem_halfRing (hs i)).and
    (eventually_ge_atTop T₀)).exists
  refine ⟨T, ⟨n, s, α, th, fun i => ⟨hT i, (h1 i).2⟩, hfs⟩, fun v => ?_⟩
  rw [hfs v]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hT i) (Conv.halfRing_mono hT₀ (hm i v))

end GlobalTheory.ArcPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEvalArcLetterRingOverDVRDiscStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eval_arcLetterRingOverDVR_disc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv : CDVR) (ϖ : Tv.V) (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (ιT : Tv.Fr →+* K), ϖ ≠ 0 → (∀ v : Tv.V, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1) → ∀ (t : K) (Y : ArcLt Dw → K), 0 < ‖t‖ → ‖t‖ < 1 → (∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => Y ⟨τ, i, k⟩).det) ≠ 0 → ∃ ev : ArcSR Dw Tv.V ϖ →+* K, (∀ p : PowerSeries Tv.V, ev (arcιR Dw Tv.V ϖ p) = ∑' k : ℕ, ιT (algebraMap Tv.V Tv.Fr (PowerSeries.coeff k p)) * t ^ k) ∧ (∀ x, ev (arcXR Dw Tv.V ϖ x) = Y x) ∧ ∀ (f : ArcSR Dw Tv.V ϖ) (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)) (P : MvPolynomial (ArcLt Dw) (LaurentSeries Tv.Fr)), f * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw Tv.V ϖ) G → P * MvPolynomial.C (HahnSeries.ofPowerSeries ℤ Tv.Fr (PowerSeries.C (R := Tv.Fr) (algebraMap Tv.V Tv.Fr ϖ) * PowerSeries.X)) ^ N = MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr))) G → Filter.Tendsto (fun k : ℤ => ‖MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k‖) Filter.cofinite (nhds 0) ∧ ev f = ∑' k : ℤ, MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k := by
  first | exact @GlobalTheory.LetterEval.exists_eval | exact GlobalTheory.LetterEval.exists_eval | (intros; apply GlobalTheory.LetterEval.exists_eval <;> assumption)
end

