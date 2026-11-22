import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPointsSpecialFibreSupportCoordinates
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSumAppellHumbert
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
noncomputable section
namespace GlobalTheory.Ex.Arch

theorem exists_symm_bilin_ext {L V : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] [AddCommGroup V]
    [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V] (P : L →+ V) (hP : Submodule.span ℝ (Set.range P) = ⊤)
    (hr : Module.finrank ℤ L = Module.finrank ℝ V) (b : L →+ (V →ₗ[ℂ] ℂ)) (hb : ∀ a c, b a (P c) = b c (P a)) :
    ∃ Bs : V →ₗ[ℂ] V →ₗ[ℂ] ℂ, (∀ u v, Bs u v = Bs v u) ∧ ∀ a v, Bs (P a) v = b a v := by
  classical
  let e := Module.Free.chooseBasis ℤ L
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range fun i => P (e i)) := by
    rw [← hP, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [← e.sum_repr a, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := fun i => P (e i)) i)) _
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Module.finrank ℝ V := by
    rw [← hr, Module.finrank_eq_card_chooseBasisIndex]
  let β := basisOfTopLeSpanOfCardEqFinrank _ htop hcard
  have hβ : ∀ i, β i = P (e i) := fun i => by simp [β]
  let f : V →ₗ[ℝ] (V →ₗ[ℂ] ℂ) := β.constr ℝ fun i => b (e i)
  have hf : ∀ a, f (P a) = b a := fun a => by
    rw [← e.sum_repr a]
    simp only [map_sum, map_zsmul, ← hβ, f, Module.Basis.constr_basis]
  have hs : ∀ u v, f u v = f v u := by
    let F : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ (fun u v => f u v) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    have : F = F.flip := β.ext fun i => β.ext fun j => by
      change f (β i) (β j) = f (β j) (β i)
      rw [hβ, hβ, hf, hf, hb]
    exact fun u v => LinearMap.congr_fun₂ this u v
  refine ⟨LinearMap.mk₂ ℂ (fun u v => f u v) (fun _ _ _ => by simp) (fun c u v => ?_) (fun _ _ _ => by simp)
    (fun _ _ _ => by simp), hs, fun a v => ?_⟩
  · rw [hs, map_smul, hs]
  · exact congrArg (fun g => g v) (hf a)

theorem hermForm_sub_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm z w - hermForm Hm w z = 2 * Complex.I * (hermForm Hm z w).im := by
  have h : ∀ i k, starRingEnd ℂ (Hm i k) = Hm k i := fun i k => hH.apply k i
  have hc : starRingEnd ℂ (hermForm Hm z w) = hermForm Hm w z := by
    simp only [hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, h, Pi.star_apply,
      RCLike.star_def, Complex.conj_conj]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [← hc, Complex.sub_conj]
  push_cast; ring

variable {O : Type} [CommRing O] [StarRing O] (B : AnArc O)

theorem lin_period (w : ℂ) (a c : B.La) : lin B a (B.Pw w c) =
    -(2 * Real.pi * Complex.I) * (B.T c.y a.y + c.n a.y + w * B.be c.y a.y) +
      Real.pi * (B.H (B.ct a.y) c.l + B.H (B.ct c.y) a.l + B.H c.l a.l) := by
  have := Complex.I_ne_zero
  rw [lin, AnArc.Pw_fst_apply, AnArc.Pw_snd, AnArc.H_add_left]
  field_simp
  ring

theorem lin_period_sub (w : ℂ) (a c : B.La) :
    lin B a (B.Pw w c) - lin B c (B.Pw w a) = -(2 * Real.pi * Complex.I) * B.EF a c := by
  have h := hermForm_sub_swap B.Hm_herm a.l c.l
  rw [← B.Ef_eq, ← B.H_def, ← B.H_def] at h
  rw [lin_period, lin_period, B.T_symm c.y, B.be_symm c.y, AnArc.EF_apply]
  push_cast at h ⊢
  linear_combination (-Real.pi : ℂ) * h

theorem perFactor_of_isPrim {w₀ : O} (hp : IsPrim B w₀) (w : ℂ) (a : B.La) (v : B.V) :
    B.perFactor w a v = (-1) ^ B.EF a (w₀ • a) * Complex.exp (lin B a v + lin B a (B.Pw w a) / 2) := by
  obtain ⟨h1, h2, h3⟩ := hp
  have hy : w₀ • a.y + star w₀ • a.y = a.y := by rw [← add_smul, h1, one_smul]
  have hT : B.T a.y a.y = 2 * B.T a.y (w₀ • a.y) := by
    have := congrArg (B.T a.y) hy
    rw [map_add, ← B.T_adj, B.T_symm (w₀ • a.y)] at this
    rw [← this]; ring
  have hE : B.EF a (w₀ • a) = B.Ef a.l (B.FLam w₀ a.l) + (a.n a.y + 2 * (-a.n (w₀ • a.y))) := by
    have := congrArg a.n hy
    rw [map_add] at this
    rw [AnArc.EF_apply, AnArc.La.smul_n_apply, AnArc.La.smul_y, AnArc.La.smul_l]
    omega
  have hq : (B.be a.y a.y : ℂ) = 2 * B.q a.y := by rw [← B.two_mul_q]; push_cast; ring
  have hs : ((-1 : ℂ)) ^ (a.n a.y + 2 * (-a.n (w₀ • a.y))) = Complex.exp (Real.pi * Complex.I * a.n a.y) := by
    rw [zpow_add₀ (by norm_num), zpow_mul, mul_comm _ (a.n a.y : ℂ), Complex.exp_int_mul, Complex.exp_pi_mul_I]
    norm_num
  rw [hE, zpow_add₀ (by norm_num), hs, AnArc.perFactor, AnArc.ah, h2, h3, lin_period, hT, hq, lin, AnArc.H_add_left,
    ← AnArc.e_add, ← AnArc.e_add, eTwoPi, ← Complex.exp_neg, mul_assoc (_ ^ _), mul_assoc (_ ^ _), ← Complex.exp_add,
    ← Complex.exp_add]
  congr 2
  ring

theorem theta_sum_appellHumbert : ThetaSt := by
  intro O _ _ B w₀ hp th hth w hS g h Hm hH hsp hE
  let b : B.La →+ (B.V →ₗ[ℂ] ℂ) := AddMonoidHom.mk' (fun a =>
    { toFun := fun v => lin B a v - Real.pi * hermForm Hm (h v) (h (B.Pw w a))
      map_add' := fun v v' => by
        simp only [lin, hermForm, map_add, add_dotProduct, Prod.fst_add, Prod.snd_add, AddMonoidHom.add_apply,
          AnArc.H_add_left]
        ring
      map_smul' := fun c v => by
        simp only [lin, hermForm, map_smul, smul_dotProduct, Prod.smul_fst, Prod.smul_snd, AddMonoidHom.smul_apply,
          AnArc.H_smul_left, smul_eq_mul, RingHom.id_apply]
        ring }) fun a a' => LinearMap.ext fun v => by
      simp only [lin, hermForm, map_add, star_add, Matrix.mulVec_add, dotProduct_add, AnArc.La.add_y, AnArc.La.add_l,
        Submodule.coe_add, AnArc.H_add_right, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
      ring
  have hb : ∀ a v, b a v = lin B a v - Real.pi * hermForm Hm (h v) (h (B.Pw w a)) := fun _ _ => rfl
  obtain ⟨Bs, hs, hB⟩ := exists_symm_bilin_ext (B.Pw w) hsp B.finrank_La b fun a c => by
    have h1 := hermForm_sub_swap hH (h (B.Pw w a)) (h (B.Pw w c))
    rw [hE] at h1
    push_cast at h1
    rw [hb, hb]
    linear_combination lin_period_sub B w a c + (Real.pi : ℂ) * h1
  refine ⟨fun z => Complex.exp (-(Bs (h.symm z) (h.symm z) / 2)) * B.Sum 1 0 th w (h.symm z), ?_, fun v => ?_,
    fun a z => ?_, fun a m hm => ?_⟩
  · have hd : Differentiable ℂ fun z => h.symm z := h.symm.toContinuousLinearEquiv.differentiable
    let Bc : B.V →L[ℂ] B.V →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap : (B.V →ₗ[ℂ] ℂ) ≃ₗ[ℂ] _).toLinearMap ∘ₗ Bs)
    have hq : Differentiable ℂ fun v : B.V => Bs v v := Bc.differentiable.clm_apply differentiable_id
    have hq' : Differentiable ℂ fun z => Bs (h.symm z) (h.symm z) := hq.comp hd
    have hq'' : Differentiable ℂ fun z => -(Bs (h.symm z) (h.symm z) / 2) := by
      simp only [div_eq_mul_inv]
      exact (hq'.mul_const _).neg
    exact hq''.cexp.mul (hS.comp hd)
  · simp only [h.symm_apply_apply, mul_eq_zero, Complex.exp_ne_zero, false_or]
  · obtain ⟨v, rfl⟩ := h.surjective z
    simp only [← map_add, h.symm_apply_apply]
    rw [B.Sum_add_period hth, pow_one, perFactor_of_isPrim B hp]
    simp only [map_add, LinearMap.add_apply, hs v (B.Pw w a), hB, hb]
    have e : ∀ s x y x' y' S : ℂ, x + y = x' + y' →
        Complex.exp x * (s * Complex.exp y * S) = s * Complex.exp x' * (Complex.exp y' * S) := fun s x y x' y' S e => by
      have := congrArg Complex.exp e
      rw [Complex.exp_add, Complex.exp_add] at this
      linear_combination s * S * this
    exact e _ _ _ _ _ _ (by ring)
  · have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
    simp only [← map_smul, h.symm_apply_apply]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hB, hb]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    field_simp
    ring

end GlobalTheory.Ex.Arch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTableAlgClosedCompleteSingleValued
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section

namespace GlobalTheory.OneBasis

variable {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F]
  [Algebra (FractionRing R) F]

theorem exists_isTorsFrame_closed [CharZero R] [IsAlgClosed F] (hLaw : Laws) {ρ : LB.Gen (A.L.pull (eSec A.A))}
    (hρ : ρ.IsGen) {n : ℕ} (hn : Odd n) (x : TFK (R := R) F ⟶ A.A) (hx : x ^ n = 1) :
    ∃ e, IsTorsFrame A ρ n x e := by
  let T := TFK (R := R) F
  have : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  obtain ⟨p⟩ : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have hu : IsUnit ((n ^ 2 : ℕ) : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.symm
    rw [← map_natCast e]
    refine (IsUnit.mk0 _ ?_).map e
    rw [← map_natCast (algebraMap R (FractionRing R))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2
      (Nat.cast_ne_zero.2 (pow_ne_zero 2 hn.pos.ne'))
  obtain ⟨y, hy⟩ : ∃ y : T ⟶ A.A, y ^ n = x :=
    TorusExt.exists_pow_eq_of_noetherian (S := Sp (FractionRing R)) (k := F) T.hom hLaw.mulN A hn.pos.ne' x
  have hy' : y ^ (n ^ 2) = 1 := by rw [sq, pow_mul, hy, hx]
  obtain ⟨hex, -⟩ := hLaw.symLift _ A (n ^ 2) hn.pow hu T y hy'
  obtain ⟨V, hV, θ₀, hθ₀⟩ := hex p
  obtain ⟨h, hh⟩ := GlobalLift.exists_section (T := T) hV
  obtain ⟨θ, hθ⟩ := GlobalLift.exists_symLift_pull A.isLB h hθ₀
  rw [← Category.assoc, hh, Category.id_comp] at hθ
  exact exists_isTorsFrame_of_symLift hLaw _ A ρ hρ n hn T y x hy' hy θ hθ

omit [IsDomain R] in

theorem exists_valAt (hLaw : Laws) {k : ℕ} (t : SecA A F k) (x : TFK (R := R) F ⟶ A.A) {e} (he : LB.Gen.IsGen e) :
    ∃ c, ValAt t x e c := by
  obtain ⟨v, hv, -⟩ := hLaw.evVal _ A k x e he t
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 v
  refine ⟨c, fun z J hJ => ?_⟩
  have := FrameMove.sval_valueAt hv (𝟙 _) hJ
  rw [Category.id_comp] at this
  exact this

end GlobalTheory.OneBasis

namespace GlobalTheory

theorem tab_full_uniq : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (m n r : ℕ), Odd m → Odd n → ∀ (th : SecA A F 1) (τ : Fin r → SecA A F (m ^ 2)), (∀ t, ∃! a, Cmb τ a t) → (tab ρ m th τ).Full (m ^ 2) n ∧ (tab ρ m th τ).Uniq (m ^ 2) n := by
  intro hLL R _ _ _ A F _ _ _ ρ hρ m n r hm hn th τ hτ
  have H := existsUnique_thetaConst hLL R A F ρ hρ
  refine ⟨⟨fun x hx => ?_, fun j x hx => ?_, fun j x hx => ?_⟩, fun x a ha => ?_, fun j x c hc => ?_⟩
  · obtain ⟨q, hq, -⟩ := H m hm th x hx
    obtain ⟨a, ha, -⟩ := hτ q.1
    exact ⟨a, hx, q.1, q.2, hq, ha⟩
  · obtain ⟨q, hq, -⟩ := H (n ^ j) hn.pow th x hx
    exact ⟨q.2, hx, q.1, hq⟩
  · obtain ⟨e, he⟩ := exists_isTorsFrame_closed A F hLL.1 hρ (hn.pow (n := j)) x hx
    choose l hl using fun i => exists_valAt A F hLL.1 (τ i) x he.2.1
    exact ⟨l, e, he, hl⟩
  · obtain ⟨hx, t, c, ht, ha⟩ := ha
    refine ⟨hx, ?_⟩
    rintro a' ⟨-, t', c', ht', ha'⟩
    have e : t' = t := congrArg Prod.fst ((H m hm th x hx).unique (y₁ := (t', c')) (y₂ := (t, c)) ht' ht)
    subst e
    exact (hτ t').unique ha' ha
  · obtain ⟨hx, t, ht⟩ := hc
    refine ⟨hx, ?_⟩
    rintro c' ⟨-, t', ht'⟩
    exact congrArg Prod.snd ((H (n ^ j) hn.pow th x hx).unique (y₁ := (t', c')) (y₂ := (t, c)) ht' ht)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionIsometryValuesIsTorsionLabelSystem
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelData

theorem labels_of_tateIsoQ : BrGtSt → BrWpSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (I : TateIsoQ D D₀ oa F) (N : NumD F) (ν : NumOf D₀ F N) (q : ∀ n : ℕ, D.La → N.QT n), (∀ n a, ν.QPt (I.ev n a) (q n a)) → Labels N D.EF I.ζ q ∧ ∀ k, 0 < k → ∀ (x : 𝓞 E) (a : D.La), ∃ z, ν.eX (q k (x • a)).1.1.toAdd = x • ν.eX (q k a).1.1.toAdd + k • z := by
  intro hG hW E _ _ _ H D R _ _ D₀ _ oa he hB F _ _ _ I N ν q hq
  obtain ⟨h1, -, h2, -, hQ⟩ := hG R D₀ he hB F N ν
  obtain ⟨hadd, htow⟩ := GlobalTheory.NestQVal.qval_add_tower E H D R D₀ oa he hB F I N ν q h1 h2
    (fun k => ⟨(hQ k).1, (hQ k).2.2⟩) hq
  refine ⟨⟨hadd, fun n hn a b => ?_, fun n hn p => ?_, htow, fun n hn a b => ?_⟩, fun n hn x a => ?_⟩
  · rw [← (hQ n).2.2 _ _ _ _ (hq n a) (hq n b)]
    exact I.ker n hn a b
  · obtain ⟨p₀, hp₀⟩ := (hQ n).2.1 p
    obtain ⟨a, ha⟩ := I.onto n hn p₀
    exact ⟨a, ((hQ n).2.2 _ _ _ _ (hq n a) hp₀).1 ha⟩
  · exact Units.ext ((hW R D₀ he hB F N ν n hn _ _ _ _ _ (hq n a) (hq n b)).1 (I.isom n hn a b)).symm
  · obtain ⟨q₀, hy, -, heq⟩ := I.lin n hn x a
    obtain ⟨c, hc, -⟩ := (hQ n).1 q₀
    obtain ⟨z, hz, -⟩ := ((hQ n).2.2 _ _ _ _ hc (hq n (x • a))).1 heq
    exact ⟨ν.eX z, by rw [hz, map_add, map_nsmul, hc.1, hy, (hq n a).1]⟩

end GlobalTheory.ModelData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionLabelSystemTwistByCompatibleRoots
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.TwistLabels
section
variable {O : Type} [CommRing O] {N : NumD O} {k : ℕ} {β : N.Form k} {u r : Oˣ} {j : ℕ}

theorem wp_eq {p q : N.QT j} {p' q' : (N.twist β u).QT j} (hp : TwRel β u r p p') (hq : TwRel β u r q q') :
    (N.twist β u).wp p' q' = N.wp p q := by
  have a : p'.1.2.s q'.1.1.toAdd = p.1.2.s q.1.1.toAdd * r ^ β.be p.1.1.toAdd q.1.1.toAdd := by
    rw [hq.1]; exact hp.2.2 _
  have b : q'.1.2.s p'.1.1.toAdd = q.1.2.s p.1.1.toAdd * r ^ β.be p.1.1.toAdd q.1.1.toAdd := by
    rw [hp.1, β.symm]; exact hq.2.2 _
  unfold NumD.wp NumD.tk
  rw [a, b, hp.2.1, hq.2.1]
  change _ * _ * cubN N.θ j 1 q.1.2.b p.1.2.b / (_ * _ * cubN N.θ j 1 p.1.2.b q.1.2.b) = _
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]
  abel

theorem rel_mul {p q : N.QT j} {p' q' : (N.twist β u).QT j} (hp : TwRel β u r p p') (hq : TwRel β u r q q') :
    TwRel β u r (p * q) (p' * q') := by
  refine ⟨?_, ?_, fun z => ?_⟩
  · change p'.1.1 * q'.1.1 = p.1.1 * q.1.1
    rw [hp.1, hq.1]; rfl
  · change p'.1.2.b * q'.1.2.b = p.1.2.b * q.1.2.b
    rw [hp.2.1, hq.2.1]; rfl
  · change p'.1.2.s z * q'.1.2.s z / N.θ (N.c z) p'.1.2.b q'.1.2.b =
      p.1.2.s z * q.1.2.s z / N.θ (N.c z) p.1.2.b q.1.2.b * r ^ β.be (p.1.1.toAdd + q.1.1.toAdd) z
    rw [hp.2.2, hq.2.2, hp.2.1, hq.2.1, map_add, LinearMap.add_apply, zpow_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]
    abel

theorem rel_inj {p q : N.QT j} {p' : (N.twist β u).QT j} (hp : TwRel β u r p p') (hq : TwRel β u r q p') : p = q := by
  have e : p.1.1 = q.1.1 := hp.1.symm.trans hq.1
  refine Subtype.ext (Prod.ext e (NumD.Gt.ext (hp.2.1.symm.trans hq.2.1) (funext fun z => ?_)))
  have := (hp.2.2 z).symm.trans (hq.2.2 z)
  rw [e] at this
  exact mul_right_cancel this

theorem rel_fun {p : N.QT j} {p' q' : (N.twist β u).QT j} (hp : TwRel β u r p p') (hq : TwRel β u r p q') : p' = q' :=
  Subtype.ext (Prod.ext (hp.1.trans hq.1.symm) (NumD.Gt.ext (hp.2.1.trans hq.2.1.symm)
    (funext fun z => (hp.2.2 z).trans (hq.2.2 z).symm)))

theorem rel_triv (h : r ^ j = u) (z : N.X) : TwRel β u r (N.qTriv j z) ((N.twist β u).qTriv j z) := by
  refine ⟨rfl, rfl, fun χ => ?_⟩
  change (N.twist β u).τ z χ = N.τ z χ * r ^ β.be (j • z) χ
  rw [N.twist_τ, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, zpow_mul, zpow_natCast, h]

theorem qEq_iff (h : r ^ j = u) {p q : N.QT j} {p' q' : (N.twist β u).QT j} (hp : TwRel β u r p p')
    (hq : TwRel β u r q q') : (N.twist β u).QEq p' q' ↔ N.QEq p q := by
  rw [NumD.qEq_iff, NumD.qEq_iff]
  refine exists_congr fun (z : N.X) => ?_
  have t := rel_mul hp (rel_triv (β := β) h z)
  exact ⟨fun e => rel_inj hq (e ▸ t), fun e => rel_fun hq (e ▸ t)⟩

theorem pow_s_eq (g : N.Gt) (g' : (N.twist β u).Gt) (hb : g'.b = g.b) (z : N.X) (t : Oˣ) (hs : g'.s z = g.s z * t)
    (m : ℕ) : (g' ^ m).s z = (g ^ m).s z * t ^ m := by
  have a := g.pow_s m z
  have b := g'.pow_s m z
  rw [hs, hb, mul_pow, ← a, mul_right_comm] at b
  exact mul_right_cancel b

theorem zpow_pow_comm (x : Oˣ) (n : ℤ) (m : ℕ) : (x ^ n) ^ m = (x ^ m) ^ n := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem rel_surj (h : r ^ j = u) (p' : (N.twist β u).QT j) : ∃ p : N.QT j, TwRel β u r p p' := by
  let y : N.X := p'.1.1.toAdd
  let g : N.Gt := ⟨p'.1.2.b, fun z => p'.1.2.s z / r ^ β.be y z, fun χ χ' => by
    have a : p'.1.2.s (χ + χ') * N.θ (N.c χ) (N.c χ') p'.1.2.b = p'.1.2.s χ * p'.1.2.s χ' := p'.1.2.mult χ χ'
    rw [map_add, zpow_add, div_mul_eq_mul_div, a, div_mul_div_comm]⟩
  have hs : ∀ z : N.X, p'.1.2.s z = g.s z * r ^ β.be y z := fun z => (div_mul_cancel _ _).symm
  have hp : p'.1.2 ^ j = (N.twist β u).io y := p'.2
  refine ⟨⟨(Multiplicative.ofAdd y, g), ?_⟩, rfl, rfl, hs⟩
  refine NumD.Gt.ext ?_ (funext fun z => ?_)
  · exact (g.pow_b j).trans ((N.twist β u).QT_pow_b p')
  · have a := pow_s_eq g p'.1.2 rfl z _ (hs z) j
    rw [hp, zpow_pow_comm, h] at a
    exact mul_right_cancel (a.symm.trans (N.twist_τ β u y z))
end

theorem labels_twist : ∀ (C : Type) [Field C] (N : NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (k₀ : ℕ) (β : N.Form k₀) (u : Cˣ) (r : ℕ → Cˣ), Roots u r → Labels N EF ζ lab → ∀ p : ∀ k : ℕ, La → (N.twist β u).QT k, (∀ k, 0 < k → ∀ x, TwRel β u (r k) (lab k x) (p k x)) → Labels (N.twist β u) EF ζ p := by
  intro C _ N La _ EF ζ lab k₀ β u r hr ⟨h1, h2, h3, h4, h5⟩ p hp
  refine ⟨fun k hk a b => ?_, fun k hk a b => ?_, fun k hk q' => ?_, fun k m hk hm a q' e1 e2 => ?_, fun k hk a b => ?_⟩
  · exact (qEq_iff (hr.pow hk) (rel_mul (hp k hk a) (hp k hk b)) (hp k hk (a + b))).2 (h1 k hk a b)
  · exact (qEq_iff (hr.pow hk) (hp k hk a) (hp k hk b)).trans (h2 k hk a b)
  · obtain ⟨q, hq⟩ := rel_surj (hr.pow hk) q'
    obtain ⟨a, ha⟩ := h3 k hk q
    exact ⟨a, (qEq_iff (hr.pow hk) (hp k hk a) hq).2 ha⟩
  · obtain ⟨q, hq⟩ := rel_surj (hr.pow hk) q'
    have t := hp (k * m) (Nat.mul_pos hk hm) a
    have e : q.1.1 = (lab (k * m) a).1.1 := hq.1.symm.trans (e1.trans t.1)
    refine (qEq_iff (hr.pow hk) hq (hp k hk a)).2 (h4 k m hk hm a q e (NumD.Gt.ext ?_ (funext fun z => ?_)))
    · rw [← hq.2.1, e2, NumD.Gt.pow_b, NumD.Gt.pow_b, t.2.1]; rfl
    · have s := pow_s_eq _ _ t.2.1 z _ (t.2.2 z) m
      rw [← e2, hq.2.2, e, zpow_pow_comm, hr.2 k m hk hm] at s
      exact mul_right_cancel s
  · exact (wp_eq (hp k hk a) (hp k hk b)).trans (h5 k hk a b)

end GlobalTheory.TwistLabels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValuesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPairing_values_of_familiesValues : BrGtSt → BrFamSt → BrWpSt := by
  first | exact @GlobalTheory.WeilValues.weil_eq_values | exact GlobalTheory.WeilValues.weil_eq_values | (intros; apply GlobalTheory.WeilValues.weil_eq_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPointsSpecialFibreSupportCoordinatesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoints_specialFibre_supportCoordinates : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → (∀ x : t.mod.Φ.Pt, x ^ (S.r * S.N) = 1 → ∃ w, Crd (t.mod.Φ.H 1) t.mod.F x.left w ∧ (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w ∈ Q.Tors (rPt p ≫ y) tm.l) ∧ ∀ v ∈ Q.Tors (rPt p ≫ y) tm.l, ∃ (x : t.mod.Φ.Pt) (w : S.J → kb p), x ^ (S.r * S.N) = 1 ∧ Crd (t.mod.Φ.H 1) t.mod.F x.left w ∧ (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w = v := by
  first | exact @GlobalTheory.ZH.TorsCrd.tors_crd | exact GlobalTheory.ZH.TorsCrd.tors_crd | (intros; apply GlobalTheory.ZH.TorsCrd.tors_crd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionActionInValues
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

noncomputable section
namespace GlobalTheory.Relabel
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Ex.GtValues

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem gtAct_pt (hG : GlobalFnsSt) {y : (TF (R := R) F).left} {J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L y J) (oa : D.OAct O) (a : O)
    {u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)}
    (hu : TorusExt.IsRos D.P.L _ _ u) (g g' : GtPtF D F) :
    GtAct oa a g g' ↔ g'.b = g.b ≫ oa.onB.act a ∧ ∀ χ,
      val (g'.s χ) (𝟙 _) y J = val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := by
  have vv : ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)) χ,
      val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 (TF (R := R) F).left) y J =
        val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := fun u χ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)))
  refine ⟨fun h => ⟨h.1, fun χ => (val_corr hJ (h.2 _ hu.1 hu.2 χ) _).symm.trans (vv _ χ)⟩,
    fun ⟨hb, hv⟩ => ⟨hb, fun u' hu' u₀ χ => corr_pt D.P.isLB (fun U _ h => ?_)
      (mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (pullGen_isGen _ _ _ _ hu' _)) (g'.isGen χ) hJ
      ((vv u' χ).trans ((congrArg₂ (· * ·) rfl
        (TorusExt.IsRos.unique hG D.P.isAb D.P.isLB ⟨hu', u₀⟩ hu hJ _ _)).trans (hv χ).symm))⟩⟩
  refine (prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _ (prod_gt g.b (star a • χ) h)
    (prod_ros _ _ (cP D _ χ) g.b h)).trans ?_
  rw [prod_gt, TorusExt.cPoint_smul oa, hb]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end

theorem gtAct_values : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : NumD F) (ν : NumOf D F N) (O : Type) [CommRing O] [StarRing O], (∀ (oa : D.P.OAct O) (x : O), ∃ ρ, RosV ν oa x ρ) ∧ ∀ [Module O D.X] (oa : D.OAct O) (x : O) (ρ : N.A → N.A → F), RosV ν oa.onB x ρ → ∀ g g' v v', ν.Pt g v → ν.Pt g' v' → (GtAct oa x g g' ↔ v'.b = actV ν oa.onB x v.b ∧ ∀ χ, (v'.s χ : F) = v.s (ν.eX.symm (star x • ν.eX χ)) * ρ (N.c χ) v.b) := by
  intro hG R _ _ D F _ _ N ν O _ _
  refine ⟨fun oa x => ?_, fun oa x ρ ⟨u, hu, u₀, hρ⟩ g g' v v' h h' => ?_⟩
  · have := oa.hom x
    have := oa.hom (star x)
    have hr := oa.rosati (star x)
    rw [star_star] at hr
    obtain ⟨u, hu, u₀⟩ := exists_ros hG D.P.isAb D.P.isLB _ _ hr
    exact ⟨_, u, hu, u₀, fun _ _ => rfl⟩
  · let y : Sp F := (⊥ : PrimeSpectrum F)
    have hJ := good ν y
    obtain ⟨a, b⟩ := (pt_iff ν y _ _).1 h
    obtain ⟨a', b'⟩ := (pt_iff ν y _ _).1 h'
    rw [gtAct_pt hG hJ oa x ⟨hu, u₀⟩, ν.eX.surjective.forall]
    refine and_congr ?_ (forall_congr' fun χ => ?_)
    · rw [← a, ← a', actV, ν.eA.eq_symm_apply]
    · have e := b (ν.eX.symm (star x • ν.eX χ))
      rw [ν.eX.apply_symm_apply] at e
      have r : toStk y (ρ (N.c χ) v.b) = (val₂ u y ν.J (cP D _ (ν.eX χ)) g.b).val := by
        rw [hρ, toStk_vF _ _ hJ, c_eq, a]; rfl
      rw [← (toStk y).injective.eq_iff, map_mul, r, ← e, ← b', ← Units.val_inj, Units.val_mul]
      rfl

end GlobalTheory.Relabel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValuesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_torsion_points_correspond_values : BrGtSt := by
  first | exact @GlobalTheory.Ex.GtValues.points_correspond | exact GlobalTheory.Ex.GtValues.points_correspond | (intros; apply GlobalTheory.Ex.GtValues.points_correspond <;> assumption)
end

