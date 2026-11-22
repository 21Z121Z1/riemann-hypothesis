import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionValuesCoordsOperatorPermute
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.EvCrd
open GlobalTheory.ThetaCompare

theorem defect_eq_one {G U : Type} [CommGroup G] [CommGroup U] (f b n : G → U) (X : G) (N M Q : ℕ) (hN : Odd N)
    (hX : X ^ N = 1) (hM : X ^ M = 1)
    (h₁ : ∀ z, f z ^ Q * (b (X * z) * (b z)⁻¹) = f 1 ^ Q * (b (X * 1) * (b 1)⁻¹))
    (h₂ : ∀ z, b z * (b z⁻¹)⁻¹ * (n z ^ Q)⁻¹ * n (z ^ M) = b 1 * (b 1⁻¹)⁻¹ * (n 1 ^ Q)⁻¹ * n (1 ^ M))
    (hp : ∏ j ∈ Finset.range N, f (X ^ j) = 1) (hs : f X⁻¹ * n 1 * (f 1 * (n X⁻¹)⁻¹) = 1) (z : G) :
    f z ^ Q * (b (X * z) * (b z)⁻¹) = 1 := by
  set κ := f 1 ^ Q * (b (X * 1) * (b 1)⁻¹) with hκ
  have e₁ : κ ^ N = 1 := by
    have : ∀ j ∈ Finset.range N, κ = f (X ^ j) ^ Q * (b (X ^ (j + 1)) / b (X ^ j)) := fun j _ => by
      rw [← h₁ (X ^ j), pow_succ' X j, div_eq_mul_inv]
    rw [show κ ^ N = ∏ _j ∈ Finset.range N, κ by rw [Finset.prod_const, Finset.card_range],
      Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_pow, hp,
      Finset.prod_range_div (fun j => b (X ^ j)) N, hX, pow_zero, div_self', one_pow, _root_.one_mul]
  have e₂ : κ ^ 2 = 1 := by
    have a₁ := h₁ X⁻¹
    have a₂ := h₂ X⁻¹
    have a₃ := congrArg (· ^ Q) hs
    rw [inv_pow, hM, inv_inv, inv_one, one_pow] at a₂
    rw [mul_inv_cancel] at a₁
    rw [_root_.mul_one] at hκ
    simp only [one_pow, mul_pow, inv_pow] at a₃
    rw [sq]
    nth_rewrite 1 [← a₁]
    rw [hκ]
    apply Additive.ofMul.injective
    replace a₂ := congrArg Additive.ofMul a₂
    replace a₃ := congrArg Additive.ofMul a₃
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at a₂ a₃ ⊢
    linear_combination (norm := module) a₃ - a₂
  obtain ⟨l, rfl⟩ := hN
  rw [pow_succ, pow_mul, e₂, one_pow, _root_.one_mul] at e₁
  exact (h₁ z).trans e₁

variable {S : Scheme.{0}}

open CommPairing GlobalLift in

theorem lift_pow (hG : GlobalFnsSt) (P : PolAV S) {T : Over S} {N M : ℕ} (hN : Odd N)
    {α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ M).left] ![(M : ℤ) ^ 2, -1])}
    (hα : α.IsGen) {x : T ⟶ P.A} (hx : x ^ N = 1) (hM : x ^ M = 1) {θ : ThetaGrp P.A P.L N T}
    (H : SymLift P.A P.L N N x θ) {y : T.left} {J} (hJ : Good P.L y J) (z : T ⟶ P.A) :
    tval θ (ptSecT P.A z).left y J ^ (M ^ 2) *
        (val α (ptSecT P.A (x * z)).left y J ^ N * (val α (ptSecT P.A z).left y J ^ N)⁻¹) = 1 := by
  have := P.isAb.comm
  obtain ⟨rfl, hp, ν, hν, hs⟩ := H
  have rα := Reg.two (y := y) (J := J) α hα (snd T P.A) (snd T P.A ^ M) rfl rfl
  have rb := rα.pow hJ N
  have rf := Reg.two (y := y) (J := J) (φ := ![(snd T P.A).left, (translPt P.A θ.pt).left]) θ.φ θ.isGen
    (snd T P.A) (translPt P.A θ.pt) rfl rfl
  have rn := Reg.two (y := y) (J := J) (φ := ![(snd T P.A).left, (snd T P.A ≫ (GrpObj.inv : P.A ⟶ P.A)).left]) ν hν
    (snd T P.A) (snd T P.A)⁻¹ rfl rfl
  have c₁ := ((rf.pow hJ (M ^ 2)).mul hJ ((rb.pull hJ (translPt P.A θ.pt)).mul hJ rb.inv)).const hG P.isAb P.isLB hJ
    (fun U _ h => by
      have q : translPt P.A θ.pt ^ M = snd T P.A ^ M := by
        rw [show translPt P.A θ.pt = (fst T P.A ≫ θ.pt) * snd T P.A from rfl, mul_pow, ← SymLiftOdd.comp_pow', hM,
          MonObj.comp_one, _root_.one_mul]
      simp only [SymLiftOdd.comp_pow', lift_snd, q]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module)
  have c₂ := (((rb.mul hJ (rb.pull hJ (snd T P.A)⁻¹).inv).mul hJ (rn.pow hJ (M ^ 2)).inv).mul hJ
    (rn.pull hJ (snd T P.A ^ M))).const hG P.isAb P.isLB hJ (fun U _ h => by
      simp only [SymLiftOdd.comp_pow', SymLiftOdd.comp_inv', lift_snd, inv_pow]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module)
  simp only [pt_translPt, SymLiftOdd.comp_pow', SymLiftOdd.comp_inv', pt_snd] at c₁ c₂
  have q₁ := val_corr hJ hp (ptSecT P.A 1).left
  have q₂ := val_corr hJ hs (ptSecT P.A 1).left
  rw [GlobalLift.val_powGen _ _ _ hJ, val_one] at q₁
  rw [GlobalLift.val_symGen _ _ _ hJ, val_one, pt_translT, pt_negT, _root_.mul_one, inv_one] at q₂
  simp only [pt_translT, _root_.mul_one] at q₁
  exact defect_eq_one (fun z => tval θ (ptSecT P.A z).left y J)
    (fun z => val α (ptSecT P.A z).left y J ^ N)
    (fun z => nval ν (ptSecT P.A z).left y J) θ.pt N M (M ^ 2) hN hx hM
    (fun z => c₁ z 1) (fun z => c₂ z 1) ((Finset.prod_range _).trans q₁) q₂ z

theorem sval_sum {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {a : ℤ} {I : Type} [Fintype I]
    {s : I → LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T)} {c : I → Γ(T.left, ⊤)}
    (H : ∀ j, s'.f j = ∑ l, liftFun A _ (c l) * (s l).f j) (x : T ⟶ A) {z : T.left} {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (ptSecT A x).left z J =
      ∑ l, gs (𝟙 _) z ⊤ (c l) *
        sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (s l) (ptSecT A x).left z J := by
  have hy := hJ.mem (fun _ : Fin 1 => (snd T A).left) (ptSecT A x).left
  refine (congrArg (gs _ z _) (H _)).trans ?_
  have hs : ∀ (W : (T ⊗ A).left.Opens) (_ : (ptSecT A x).left z ∈ W) (u : I → Γ((T ⊗ A).left, W)),
      gs (ptSecT A x).left z W (∑ l, u l) = ∑ l, gs (ptSecT A x).left z W (u l) := fun W hW u => by
    simp only [gs_eq _ z W hW, map_sum]
  refine (hs _ hy _).trans (Finset.sum_congr rfl fun l _ => (gs_mul _ z _ hy _ _).trans (congrArg (· * _) ?_))
  refine (gs_res _ z _ hy _).trans ((gs_pull _ (fst T A).left z ⊤ trivial _).trans ?_)
  rw [← Over.comp_left, ptSecT, lift_fst]; rfl

open CommPairing in

theorem exists_root_stalk (hG : GlobalFnsSt) (P : PolAV S) {T : Over S} {N M : ℕ} (hN : Odd N)
    {rig : LB.Gen (P.L.pull (eSec P.A))} {x h w : T ⟶ P.A} (hx : x ^ N = 1) (hM : x ^ M = 1) (hw : w = x * h)
    {θ : ThetaGrp P.A P.L N T} (H : SymLift P.A P.L N N x θ) {τ τ'} (hτ : IsTorsFrame P rig M h τ)
    (hτ' : IsTorsFrame P rig M w τ') (y : T.left) :
    ∃ ξ : (T.left.presheaf.stalk y)ˣ, ξ ^ (M ^ 2) = 1 ∧
      ∀ (I : Type) [Fintype I] (s : I → LB.Sec (LPow P.A P.L N T)) (t : LB.Sec (LPow P.A P.L N T))
        (c v : I → Γ(T.left, ⊤)) (v' : Γ(T.left, ⊤)),
        (∀ σ, IsActOf P.A P.L N θ t σ → ∀ j, σ.f j = ∑ l, liftFun P.A _ (c l) * (s l).f j) →
        (∀ l, IsValueAt P.A P.L N (s l) h (powFrame P.A P.L h τ N) (v l)) →
        IsValueAt P.A P.L N t w (powFrame P.A P.L w τ' N) v' →
        ∑ l, gs (𝟙 _) y ⊤ (c l) * gs (𝟙 _) y ⊤ (v l) = ξ.val * gs (𝟙 _) y ⊤ v' := by
  subst hw
  choose J hJ using fun χ : T.left ⟶ P.A.left => exists_chart P.isLB (χ y)
  replace hJ : Good P.L y J := hJ
  obtain ⟨β, hβ, -⟩ := hτ.2.2
  obtain ⟨α, hα, -⟩ := VVRank.exists_gen_pullTo (φ' := ![(snd T P.A).left, (snd T P.A ^ M).left]) β hβ
    (snd T P.A).left (fun k => by
      fin_cases k
      · exact Category.comp_id _
      · change (snd T P.A).left ≫ (mulA P.A M).left = (snd T P.A ^ M).left
        rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id])
  have a₁ := lift_pow hG P hN hα hx hM H hJ h
  have a₂ := torsFrame_pow hG P hα hτ hJ
  have a₃ := torsFrame_pow hG P hα hτ' hJ
  refine ⟨tval θ (ptSecT P.A h).left y J * val τ' (𝟙 _) y J ^ N * (val τ (𝟙 _) y J ^ N)⁻¹, ?_,
    fun I _ s t c v v' hc hv hv' => ?_⟩
  · apply Additive.ofMul.injective
    replace a₁ := congrArg Additive.ofMul a₁
    replace a₂ := congrArg Additive.ofMul a₂
    replace a₃ := congrArg Additive.ofMul a₃
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at a₁ a₂ a₃ ⊢
    linear_combination (norm := module) a₁ + N • a₃ - N • a₂
  · obtain ⟨σ, hσ⟩ : ∃ σ, IsActOf P.A P.L (N : ℤ) θ t σ := VVRank.exists_isTwistPull P.A P.isLB θ.isGen t
    have p : ∀ (z : T ⟶ P.A) (e), val (powFrame P.A P.L z e N) (𝟙 _) y J = val e (𝟙 _) y J ^ N := fun z e =>
      (map_zpow _ _ _).trans (zpow_natCast _ _)
    have b₁ := sval_twist hσ (ptSecT P.A h).left hJ
    have b₂ := sval_sum (hc σ hσ) h hJ
    have b₃ := sval_valueAt hv' hJ
    rw [pt_translT, congrArg (fun q => ptSecT P.A (q * h)) H.pt_eq, b₃, b₂, p] at b₁
    simp only [fun l => sval_valueAt (hv l) hJ, p, ← _root_.mul_assoc, ← Finset.sum_mul] at b₁
    rw [(Units.eq_mul_inv_iff_mul_eq _).2 b₁, Units.val_mul, Units.val_mul]
    change (tval θ (ptSecT P.A h).left y J).val * _ * _ * _ = _
    ring

theorem valR_comp {R : Type} [CommRing R] {X Y : Scheme.{0}} (x : Sp R ⟶ Y) (g : Y ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ g ⁻¹ᵁ U) (f : Γ(X, U)) : valR x (g ⁻¹ᵁ U) ((g.app U).hom f) = valR (x ≫ g) U f := by
  rw [CrdCalc.valR_eq x _ h, CrdCalc.valR_eq (x ≫ g) U h]
  rfl

theorem valR_fn {R K : Type} [CommRing R] [CommRing K] (y : R →+* K) (b : R) : valR (spMap y) ⊤ (fn b) = y b := by
  rw [CrdCalc.valR_eq _ _ le_rfl]
  have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y)
  have e := congrArg (fun q => q.hom b) n
  change (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (y b) = (spMap y).appTop.hom (fn b) at e
  have e' : ((spMap y).appLE ⊤ ⊤ le_rfl) = (spMap y).appTop := (Scheme.Hom.app_eq_appLE _).symm
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (((spMap y).appLE ⊤ ⊤ le_rfl).hom (fn b)) = _
  rw [e', ← e]
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id_apply _

theorem crd_of_isValueAt {R K : Type} [CommRing R] [Field K] (y : R →+* K) (P : PolAV (Sp R)) {k : ℤ} {I : Type}
    {s : I → LB.Sec (LPow P.A P.L k (baseOver (Sp R)))} {z : baseOver (Sp R) ⟶ P.A} {τ} {v : I → R}
    (H : ∀ i, IsValueAt P.A P.L k (s i) z τ (fn (v i))) :
    Crd (LPow P.A P.L k (baseOver (Sp R))) s (spMap y ≫ (ptSecT P.A z).left) (fun i => y (v i)) := by
  let x : Sp K ⟶ (baseOver (Sp R)).left := spMap y
  obtain ⟨j₀, hj⟩ := exists_chart P.isLB (z.left (x (IsLocalRing.closedPoint K)))
  let W := LB.wchart P.L (fun _ : Fin 1 => z.left) (fun _ => j₀)
  have hW : ⊤ ≤ x ⁻¹ᵁ W := (CrdCalc.top_le_iff x W).2 (Set.mem_iInter.2 fun _ => hj)
  have hU := hW.trans (x.preimage_mono (val_le P.A P.L z (fun _ => j₀)))
  refine ⟨fun _ => j₀, (Units.map (CrdCalc.valHom x W hW).toMonoidHom (τ.s fun _ => j₀))⁻¹, hU, fun i => ?_⟩
  have e := congrArg (valR x W) (H i fun _ => j₀)
  have e₁ := ((CrdCalc.valR_res x (val_le P.A P.L z (fun _ => j₀)) hW _).trans
    (valR_comp x (ptSecT P.A z).left _ hU ((s i).f fun _ => j₀))).symm.trans e
  have e₂ := e₁.trans ((CrdCalc.valR_mul x W hW _ _).trans (congrArg₂ (· * ·)
    ((CrdCalc.valR_res x le_top hW _).trans (valR_fn y (v i))) (CrdCalc.valR_eq x W hW _)))
  refine (Units.eq_inv_mul_iff_mul_eq _).2 ?_
  exact (mul_comm _ _).trans e₂.symm

theorem ev_crd_act : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), (∀ (K : Type) [Field K] (y : S.R →+* K) (a : S.Gam), ρ.Crd (spMap y ≫ (ρ.pt a).left) (fun i => y ⟨S.ev a i, S.ev_mem a i⟩)) ∧ ∀ a h : S.Gam, ∃ e : ℕ, ∀ i, ∑ n, algebraMap o Ω (S.ρ a n i) * S.ev h n = algebraMap o Ω (S.ζ ^ e) * S.ev (h + S.r • a) i := by
  intro hL o Ω _ _ _ hb S ρ
  refine ⟨fun K _ y a => ⟨_, ?_, crd_of_isValueAt y ρ.P (fun i => ρ.ev_val i a)⟩, fun a h => ?_⟩
  · rw [Category.assoc, ← Over.comp_left, pt_snd]
  have := ρ.P.isAb.comm
  have hN : Odd S.N := by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow
  have h₀ : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hp : ∀ (n : ℕ) b, ρ.pt (n • b) = ρ.pt b ^ n := fun n b => by
    induction n with
    | zero => rw [zero_smul, h₀, pow_zero]
    | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]
  have hx : ρ.pt (S.r • a) ^ S.N = 1 := by rw [hp, ← pow_mul, (ρ.fr_tors a).1]
  let iso := Scheme.ΓSpecIso (CommRingCat.of S.R)
  let y : Sp S.R := (⊥ : PrimeSpectrum S.R)
  obtain ⟨ξ, hξ, e⟩ := exists_root_stalk hL.1.globalFns ρ.P hN hx (ρ.fr_tors _).1
    (by rw [ρ.pt_add, mul_comm]) (ρ.U_sym a) (ρ.fr_tors h) (ρ.fr_tors (h + S.r • a)) y
  let g : S.R →+* (Sp S.R).presheaf.stalk y := ((Sp S.R).presheaf.germ ⊤ y trivial).hom.comp iso.inv.hom
  have hg : Function.Injective g :=
    (germ_injective_of_isIntegral (Sp S.R) (U := ⊤) y trivial).comp (ConcreteCategory.bijective_of_isIso iso.inv).1
  have hgs : ∀ b : S.R, gs (𝟙 (baseOver (Sp S.R)).left) y ⊤ (fn b) = g b := fun b => gs_eq _ y ⊤ trivial _
  have hi : Function.Injective (algebraMap o S.R) := fun b b' h => hb.inj (congrArg Subtype.val h)
  have hζ : IsPrimitiveRoot (g (algebraMap o S.R S.ζ)) ((S.r * S.N) ^ 2) :=
    (S.prim.map_of_injective hi).map_of_injective hg
  have : NeZero ((S.r * S.N) ^ 2) := ⟨(pow_pos (Nat.mul_pos S.r_pos hN.pos) 2).ne'⟩
  have : IsDomain ((baseOver (Sp S.R)).left.presheaf.stalk y) := inferInstanceAs (IsDomain ((Sp S.R).presheaf.stalk y))
  obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one (ξ := ξ.val) (congrArg Units.val hξ)
  refine ⟨k, fun i => ?_⟩
  have e' := e S.J ρ.s (ρ.s i) _ _ _ (ρ.U_act a i) (fun l => ρ.ev_val l h) (ρ.ev_val i _)
  simp only [hgs] at e'
  have q : ∑ n, algebraMap o S.R (S.ρ a n i) * ⟨S.ev h n, S.ev_mem _ _⟩ =
      algebraMap o S.R (S.ζ ^ k) * ⟨S.ev (h + S.r • a) i, S.ev_mem _ _⟩ := hg (by
    rw [map_sum, map_mul, map_pow, map_pow, hk]
    simp only [map_mul]
    exact e')
  have q' := congrArg S.R.val q
  rw [map_sum] at q'
  exact q'

end GlobalTheory.ZH.EvCrd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusCutByInvariantRatiosField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.KerCut

theorem hom_ext_of_appLE {X Y : Scheme.{0}} (V : X.Opens) (hV : IsAffineOpen V) (f g : Y ⟶ X)
    (hf : ⊤ ≤ f ⁻¹ᵁ V) (hg : ⊤ ≤ g ⁻¹ᵁ V) (e : f.appLE V ⊤ hf = g.appLE V ⊤ hg) : f = g := by
  have : IsAffine V.toScheme := hV
  have r : ∀ (f : Y ⟶ X), ⊤ ≤ f ⁻¹ᵁ V → ∃ f' : Y ⟶ V.toScheme, f = f' ≫ V.ι := by
    intro f hf
    refine ⟨IsOpenImmersion.lift V.ι f ?_, (IsOpenImmersion.lift_fac _ _ _).symm⟩
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact hf (show y ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨f', ef⟩ := r f hf
  obtain ⟨g', eg⟩ := r g hg
  rw [← GlobalTheory.FunDescent.res_comp_appTop V f' f ef, ← GlobalTheory.FunDescent.res_comp_appTop V g' g eg] at e
  have : f' = g' := by
    apply ext_of_isAffine
    ext x
    obtain ⟨y, rfl⟩ := (GlobalTheory.FunDescent.res_bijective V).2 x
    exact congrArg (fun ψ => ψ.hom y) e
  rw [ef, eg, this]

theorem appLE_appLE_apply {X Y Z : Scheme.{0}} (k : Z ⟶ Y) (q : Y ⟶ X) (V : X.Opens) (W : Y.Opens)
    (h : W ≤ q ⁻¹ᵁ V) (h' : ⊤ ≤ k ⁻¹ᵁ W) (p : Z ⟶ X) (e : k ≫ q = p) (h'' : ⊤ ≤ p ⁻¹ᵁ V) (v : Γ(X, V)) :
    (k.appLE W ⊤ h').hom ((q.appLE V W h).hom v) = (p.appLE V ⊤ h'').hom v := by
  subst e
  rw [← Scheme.Hom.appLE_comp_appLE k q V W ⊤ h h']
  rfl

end GlobalTheory.ZJ.KerCut

namespace GlobalTheory.ZJ

theorem Charts.kerIs_of_torus : ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H) (a) (j : Fin d → C.I), GeometricallyConnected H.hom → C.Torus c i → C.Based c a j → C.KerIs a j i := by
  intro K _ H _ _ _ _ _ C d c i a j hc hT hB
  obtain ⟨B, _, q, -, hq, -, -, -, hP, hV⟩ := GlobalTheory.T.splitCharts_torus_extension_over_field K H C d c i hc hT
  obtain ⟨V, hW, hVa, hu⟩ := hV a
  have one_mem : ∀ Y : Over (Sp K), ⊤ ≤ (1 : Y ⟶ H).left ⁻¹ᵁ C.W a := by
    intro Y y _
    exact hB.1 (show (toUnit Y).left y ∈ (⊤ : (Sp K).Opens) from trivial)
  refine ⟨⟨fun {Y} s t e => hP.hom_ext e (toUnit_unique _ _)⟩, fun Y k => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨h, h₁, hr⟩
    have key : k ≫ q = (1 : Y ⟶ H) ≫ q := by
      apply Over.OverMorphism.ext
      have m : ∀ g : Y ⟶ H, ⊤ ≤ g.left ⁻¹ᵁ C.W a → ⊤ ≤ (g ≫ q).left ⁻¹ᵁ V := by
        intro g hg
        rw [hW] at hg
        exact hg
      refine KerCut.hom_ext_of_appLE V hVa _ _ (m k h) (m 1 h₁) ?_
      ext v
      have hv := hT.gen a _ ((hu _).2 ⟨v, rfl⟩)
      have eq := RingHom.eqOn_set_closure (f := (k.left.appLE _ ⊤ h).hom)
        (g := ((1 : Y ⟶ H).left.appLE _ ⊤ h₁).hom) (by
          rintro u (⟨w, rfl⟩ | ⟨j', hj', rfl⟩)
          · exact (KerCut.appLE_appLE_apply _ _ _ _ _ _ Y.hom (Over.w k) le_rfl w).trans
              (KerCut.appLE_appLE_apply _ _ _ _ _ _ Y.hom (Over.w _) le_rfl w).symm
          · exact hr j' hj') hv
      exact (KerCut.appLE_appLE_apply _ _ _ _ _ _ _ rfl (m k h) v).symm.trans
        (eq.trans (KerCut.appLE_appLE_apply _ _ _ _ _ _ _ rfl (m 1 h₁) v))
    have w : k ≫ q = toUnit Y ≫ η[B] := by
      rw [key, MonObj.one_comp]
      rfl
    exact ⟨hP.lift _ _ w, (hP.lift_fst _ _ w).symm⟩
  · rintro ⟨t, rfl⟩
    have h' := hT.stable a Y t 1 (one_mem Y)
    have hr := fun j' hj' => hT.inv a j' hj' Y t 1 (one_mem Y) h'
    revert h' hr
    rw [_root_.mul_one]
    intro h' hr
    refine ⟨h', one_mem Y, fun j' hj' => ?_⟩
    rw [hr j' hj', charUnit_zero_val, map_one, _root_.one_mul]
  · intro Y t n h h₁
    have := hT.wt a (j n) n (hB.2 n).1 Y t 1 h₁
    rw [_root_.mul_one] at this
    exact this h

end GlobalTheory.ZJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedPowerSectionBasisBaseChange
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.BasisBaseChange

open GlobalTheory.FieldBaseChange

section Algebra

variable {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R' M']

theorem basis_map_of_basis {φ : R →+* R'} (f : M →ₛₗ[φ] M') {I J : Type} [Fintype I] [Fintype J]
    (b : J → M) (β : I → M) (hb : ∀ s, ∃! a : J → R, s = ∑ j, a j • b j)
    (hβ : ∀ s, ∃! a : I → R, s = ∑ i, a i • β i)
    (hf : ∀ s, ∃! a : J → R', s = ∑ j, a j • f (b j)) (s : M') : ∃! a : I → R', s = ∑ i, a i • f (β i) := by
  classical
  choose u hu _ using fun i => hb (β i)
  choose w hw _ using fun j => hβ (b j)
  have huw : ∀ i i', ∑ j, u i j * w j i' = if i = i' then 1 else 0 := fun i => by
    have h1 : β i = ∑ i', (∑ j, u i j * w j i') • β i' := by
      conv_lhs => rw [hu i]
      simp only [Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [← Finset.smul_sum, ← hw j]
    have h2 : β i = ∑ i', (if i = i' then (1 : R) else 0) • β i' := by simp
    exact congrFun ((hβ (β i)).unique h1 h2)
  have fβ : ∀ a : I → R', ∑ i, a i • f (β i) = ∑ j, (∑ i, a i * φ (u i j)) • f (b j) := fun a => by
    simp only [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.smul_sum, hu i, map_sum]
    simp only [map_smulₛₗ, ← hu i]
  have fb : ∀ c : J → R', ∑ j, c j • f (b j) = ∑ i, (∑ j, c j * φ (w j i)) • f (β i) := fun c => by
    simp only [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.smul_sum, hw j, map_sum]
    simp only [map_smulₛₗ, ← hw j]
  have back : ∀ (a : I → R') i', ∑ j, (∑ i, a i * φ (u i j)) * φ (w j i') = a i' := fun a i' => by
    simp only [Finset.sum_mul, _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ← map_sum, huw]
    simp [apply_ite φ]
  obtain ⟨c, hc, hcu⟩ := hf s
  refine ⟨_, hc.trans (fb c), fun a ha => funext fun i => ?_⟩
  rw [← hcu _ (ha.trans (fβ a)), back]

end Algebra

theorem isLin_iff {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Sp R) {H : LB Y} {I : Type} [Fintype I]
    (s : I → SecOver p H) (a : I → R) (t : SecOver p H) : IsLin p s a t ↔ t = ∑ i, a i • s i := by
  have e : ∀ l, chartFun p H l (∑ i, a i • s i) = ∑ i, a i • chartFun p H l (s i) := fun l =>
    (map_sum (chartLin p H l) _ _).trans rfl
  exact ⟨fun h => SecOver.ext _ _ fun l => (h l).trans (e l).symm, fun h l => (congrArg (chartFun p H l) h).trans (e l)⟩

theorem basis_of_isPullback {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {A : Over (Sp R)}
    {L : LB A.left} (hL : L.IsLB) {K : Type} [Fintype K] (ψ : K → (A.left ⟶ A.left)) (ε : K → ℤ) {m : ℕ}
    (b : Fin m → SecOver A.hom (LB.LinComb L ψ ε))
    (hb : IsSecBasis (T := Over.mk (spMap φ)) (A := A) _
      (fun i => DVR.pullSec L ψ ε (b i) (snd (Over.mk (spMap φ)) A).left))
    {B : Scheme.{0}} {pB : B ⟶ Sp R'} {π : B ⟶ A.left} (H : IsPullback π pB A.hom (spMap φ))
    {ψ' : K → (B ⟶ A.left)} (hψ : ∀ k, ψ' k = π ≫ ψ k) (s : SecOver pB (LB.LinComb L ψ' ε)) :
    ∃! a : Fin m → R', s = ∑ i, a i • pullOver L ε H.w hψ (b i) := by
  let T : Over (Sp R) := Over.mk (spMap φ)
  let p : (T ⊗ A).left ⟶ Sp R' := (fst T A).left
  let q : (T ⊗ A).left ⟶ A.left := (snd T A).left
  have H' : IsPullback q p A.hom (spMap φ) := (IsPullback.of_hasPullback (spMap φ) A.hom).flip
  let e := H.isoIsPullback _ _ H'
  have e1 : e.hom ≫ q = π := H.isoIsPullback_hom_fst _ _ H'
  have e2 : e.hom ≫ p = pB ≫ Spec.map (CommRingCat.ofHom (RingHom.id R')) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]; exact H.isoIsPullback_hom_snd _ _ H'
  have e3 : e.inv ≫ π = q := H.isoIsPullback_inv_fst _ _ H'
  have e4 : e.inv ≫ pB = p ≫ Spec.map (CommRingCat.ofHom (RingHom.id R')) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]; exact H.isoIsPullback_inv_snd _ _ H'
  have f1 : ∀ k, ψ' k = e.hom ≫ (q ≫ ψ k) := fun k => by rw [hψ, ← e1, Category.assoc]
  have f2 : ∀ k, q ≫ ψ k = e.inv ≫ ψ' k := fun k => by rw [hψ, ← e3, Category.assoc]
  let F := pullOver L ε e2 (φ := fun k => q ≫ ψ k) f1
  let G := pullOver L ε e4 (φ' := fun k => q ≫ ψ k) f2
  let b' : Fin m → SecOver p (LB.LinComb L (fun k => q ≫ ψ k) ε) := fun i => DVR.pullSec L ψ ε (b i) q
  have FG : ∀ t, F (G t) = t := fun t => sec_ext' hL fun y J hJ => by
    rw [sval_pullOver e2 f1 _ _ hJ, sval_pullOver e4 f2 _ _ hJ, Category.assoc, e.hom_inv_id, Category.comp_id]
  have GF : ∀ t, G (F t) = t := fun t => sec_ext' hL fun y J hJ => by
    rw [sval_pullOver e4 f2 _ _ hJ, sval_pullOver e2 f1 _ _ hJ, Category.assoc, e.inv_hom_id, Category.comp_id]
  have Fb : ∀ i, F (b' i) = pullOver L ε H.w hψ (b i) := fun i => sec_ext' hL fun y J hJ => by
    rw [sval_pullOver e2 f1 _ _ hJ, sval_pullOver H.w hψ _ _ hJ]
    exact (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ).trans (by rw [Category.assoc, e1])
  have hb' : ∀ t : SecOver p (LB.LinComb L (fun k => q ≫ ψ k) ε), ∃! a : Fin m → R', t = ∑ i, a i • b' i := by
    intro t
    obtain ⟨r, hr, hu⟩ := hb t
    have e : ∀ i, (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom (r i)) = r i := fun i => Iso.hom_inv_id_apply _ _
    refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom (r i), (isLin_iff p _ _ _).1 fun j => ?_,
      fun a ha => ?_⟩
    · refine (hr j).trans (Finset.sum_congr rfl fun i _ => ?_)
      simp only [constFn, e]
      rfl
    · have := hu (fun i => (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (a i)) ((isLin_iff p _ _ _).2 ha)
      funext i
      rw [← this]
      exact (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of R')) (a i)).symm
  have Fs : ∀ a : Fin m → R', F (∑ i, a i • b' i) = ∑ i, a i • pullOver L ε H.w hψ (b i) := fun a => by
    simp only [map_sum, map_smulₛₗ, Fb, RingHom.id_apply]
  obtain ⟨a, ha, hu⟩ := hb' (G s)
  refine ⟨a, ?_, fun a' ha' => hu a' ?_⟩
  · show s = _
    rw [← Fs, ← ha, FG]
  · show G s = _
    rw [ha', ← Fs, GF]

theorem basis_pullback : DVR.TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R) (N : ℕ), 1 ≤ N → ∀ (α : D.X) (R' : Type) [CommRing R'] (φ : R →+* R') (B : Scheme.{0}) (pB : B ⟶ Sp R') (π : B ⟶ D.P.A.left), IsPullback π pB D.P.A.hom (spMap φ) → ∀ (I : Type) [Fintype I] (β : I → D.SecB N α), IsBasisB D β → ∀ b : LB.Sec (LB.LinComb D.P.L (fun i => π ≫ D.famφB α i) (DegPre.famε N)), ∃! a : I → R', IsLin pB (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε N) (β i) π) a b := by
  intro hT R _ _ _ _ D N hN α R' _ φ B pB π H I _ β hβ s
  have hL := D.P.isLB
  obtain ⟨m, b, -, hb⟩ := hT R D N hN α
  have H₀ : IsPullback (𝟙 D.P.A.left) D.P.A.hom D.P.A.hom (spMap (RingHom.id R)) := by
    have : spMap (RingHom.id R) = 𝟙 _ := by simp [spMap]
    rw [this]
    exact IsPullback.id_horiz _
  have hψ₀ : ∀ k, D.famφB α k = 𝟙 _ ≫ D.famφB α k := fun k => (Category.id_comp _).symm
  have h0 := basis_of_isPullback (RingHom.id R) hL (D.famφB α) (DegPre.famε N) b
    (hb R (RingHom.id R) _ fun _ _ => rfl) H₀ hψ₀
  have e0 : ∀ i, pullOver D.P.L (DegPre.famε N) H₀.w hψ₀ (b i) = b i := fun i => sec_ext' hL fun y J hJ =>
    (sval_pullOver H₀.w hψ₀ _ _ hJ).trans (by rw [Category.comp_id])
  simp only [e0] at h0
  have hψ : ∀ k, (fun i => π ≫ D.famφB α i) k = π ≫ D.famφB α k := fun _ => rfl
  have h1 := basis_of_isPullback φ hL (D.famφB α) (DegPre.famε N) b (hb R' φ _ fun _ _ => rfl) H hψ
  have h2 := basis_map_of_basis (pullOver D.P.L (DegPre.famε N) H.w hψ) b β h0
    (fun t => (existsUnique_congr fun a => isLin_iff D.P.A.hom β a t).1 (hβ t)) h1 s
  have e1 : ∀ i, pullOver D.P.L (DegPre.famε N) H.w hψ (β i) =
      DVR.pullSec D.P.L (D.famφB α) (DegPre.famε N) (β i) π := fun i => sec_ext' hL fun y J hJ =>
    (sval_pullOver H.w hψ _ _ hJ).trans (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ).symm
  simp only [e1] at h2
  exact (existsUnique_congr fun a => isLin_iff pB _ a s).2 h2

end GlobalTheory.ZH.BasisBaseChange
end
end

