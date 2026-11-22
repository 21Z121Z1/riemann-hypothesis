import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0088
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0315
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0411
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0223
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0405
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0362
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0328
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0429
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0419

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteClassesRationalIsometriesBoundedDenominato
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx.QFin

section Lemmas

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem mulVec_mul (g h : GL (Fin r) E) (v : Fin r → E) :
    ((g * h : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v =
      (g : Matrix (Fin r) (Fin r) E) *ᵥ ((h : Matrix (Fin r) (Fin r) E) *ᵥ v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem mulVec_inv_mulVec (g : GL (Fin r) E) (v : Fin r → E) :
    ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((g : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := by
  rw [← mulVec_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_mulVec_inv (g : GL (Fin r) E) (v : Fin r → E) :
    (g : Matrix (Fin r) (Fin r) E) *ᵥ (((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := by
  rw [← mulVec_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

variable {X X' : Data E r} {N : ℕ}

theorem qmatch_stab_mul {a g : GL (Fin r) E} (h : QMatch X X' N a) (hg : IsUStab X'.Gm X'.Λ g) :
    QMatch X X' N (g * a) := by
  refine ⟨h.psi, h.p0, h.xi, fun u v => ?_, fun v hv => ?_, fun w hw => ?_⟩
  · rw [mulVec_mul, mulVec_mul, hg.1, h.iso]
  · rw [mulVec_mul, ← Matrix.mulVec_smul]
    exact (hg.2 _).1 (h.lat v hv)
  · rw [mul_inv_rev, mulVec_mul]
    exact h.lat' _ ((hg.2 _).2 (by rw [mulVec_mulVec_inv]; exact hw))

def InL (X' : Data E r) (N : ℕ) (a : GL (Fin r) E) (v : Fin r → E) : Prop :=
  (N : E)⁻¹ • ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) ∈ X'.Λ

theorem inL_transfer (hN : 0 < N) {a a' : GL (Fin r) E} (h' : QMatch X X' N a')
    (hP : ∀ v ∈ X.Λ, InL X' N a' v → InL X' N a v) {w : Fin r → E} (hw : w ∈ X'.Λ) :
    ((a * a'⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w ∈ X'.Λ := by
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have key : ∀ g : GL (Fin r) E, (N : E)⁻¹ • ((g : Matrix (Fin r) (Fin r) E) *ᵥ
      ((N : E) • (((a'⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w))) =
      (g : Matrix (Fin r) (Fin r) E) *ᵥ (((a'⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) := by
    intro g
    rw [Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hN', one_smul]
  have h1 := hP _ (h'.lat' w hw) (by unfold InL; rw [key, mulVec_mulVec_inv]; exact hw)
  unfold InL at h1
  rw [key] at h1
  rw [mulVec_mul]
  exact h1

theorem isUStab_of_inL (hN : 0 < N) {a a' : GL (Fin r) E} (h : QMatch X X' N a) (h' : QMatch X X' N a')
    (hP : ∀ v ∈ X.Λ, InL X' N a v ↔ InL X' N a' v) : IsUStab X'.Gm X'.Λ (a * a'⁻¹) := by
  refine ⟨fun x y => ?_, fun x => ⟨fun hx => inL_transfer hN h' (fun v hv => (hP v hv).2) hx, fun hx => ?_⟩⟩
  · rw [mulVec_mul, mulVec_mul, h.iso, ← h'.iso, mulVec_mulVec_inv, mulVec_mulVec_inv]
  · have := inL_transfer hN h (fun v hv => (hP v hv).1) hx
    rwa [mulVec_mul, mulVec_mul, mulVec_inv_mulVec, mulVec_mulVec_inv] at this

end Lemmas

theorem finite_reps (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ)
    (hN : 0 < N) : ∃ S : Finset (GL (Fin r) E), (∀ s ∈ S, QMatch X X' N s) ∧
      ∀ a, QMatch X X' N a → ∃ s ∈ S, ∃ b ∈ X'.Γ, a = b * s := by
  classical
  have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set A := X.Λ.toAddSubgroup
  have hfg : A.FG := by
    haveI : Module.Finite (𝓞 E) X.Λ := Module.Finite.iff_fg.2 X.Λ_fg
    haveI : Module.Finite ℤ X.Λ := Module.Finite.trans (𝓞 E) X.Λ
    exact (AddGroup.fg_iff_addSubgroup_fg _).1 (Module.Finite.iff_addGroup_fg.1 this)
  haveI : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
  set K := (nsmulAddMonoidHom (α := A) (N * N)).range
  haveI : K.FiniteIndex := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg A (mul_ne_zero hN.ne' hN.ne')
  haveI : Fintype (Set (A ⧸ K)) := Fintype.ofFinite _
  let f : GL (Fin r) E → Set (A ⧸ K) := fun a =>
    (QuotientAddGroup.mk : A → A ⧸ K) '' {v | InL X' N a (v : Fin r → E)}
  have hf : ∀ a, QMatch X X' N a → ∀ v : A,
      (QuotientAddGroup.mk v : A ⧸ K) ∈ f a ↔ InL X' N a (v : Fin r → E) := by
    intro a ha v
    constructor
    · rintro ⟨v', hv', he⟩
      obtain ⟨u, hu⟩ := QuotientAddGroup.eq.1 he
      have hv : (v : Fin r → E) = (v' : Fin r → E) + ((N : E) * N) • (u : Fin r → E) := by
        have := congrArg (fun z : A => (z : Fin r → E)) hu
        simp only [nsmulAddMonoidHom_apply, AddSubgroup.coe_add, AddSubgroup.coe_neg,
          AddSubgroup.coe_nsmul] at this
        rw [← Nat.cast_mul, Nat.cast_smul_eq_nsmul, this]
        abel
      show InL X' N a (v : Fin r → E)
      have hv'' : InL X' N a (v' : Fin r → E) := hv'
      unfold InL at hv'' ⊢
      rw [hv, Matrix.mulVec_add, Matrix.mulVec_smul, smul_add, smul_smul, ← _root_.mul_assoc,
        inv_mul_cancel₀ hN0, _root_.one_mul]
      exact X'.Λ.add_mem hv'' (ha.lat _ u.2)
    · intro h
      exact ⟨v, h, rfl⟩
  let rep : Set (A ⧸ K) → GL (Fin r) E := fun T =>
    if h : ∃ a, QMatch X X' N a ∧ f a = T then h.choose else 1
  obtain ⟨S0, hS0⟩ := X'.Γ_index
  refine ⟨((Finset.univ ×ˢ S0).image fun p => p.2⁻¹ * rep p.1).filter (QMatch X X' N),
    fun s hs => (Finset.mem_filter.1 hs).2, fun a ha => ?_⟩
  have hex : ∃ a', QMatch X X' N a' ∧ f a' = f a := ⟨a, ha, rfl⟩
  have hrep : rep (f a) = hex.choose := dif_pos hex
  obtain ⟨ha', hfa⟩ := hex.choose_spec
  have hP : ∀ v ∈ X.Λ, InL X' N hex.choose v ↔ InL X' N a v := by
    intro v hv
    rw [← hf _ ha' ⟨v, hv⟩, ← hf a ha ⟨v, hv⟩, hfa]
  obtain ⟨s, hs, hsΓ⟩ := hS0 _ (isUStab_of_inL hN ha' ha hP)
  have hq := qmatch_stab_mul ha (X'.Γ_stab _ hsΓ)
  have e : s⁻¹ * (hex.choose * a⁻¹) * a = s⁻¹ * hex.choose := by group
  rw [e] at hq
  refine ⟨s⁻¹ * hex.choose, Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(f a, s),
    Finset.mem_product.2 ⟨Finset.mem_univ _, hs⟩, ?_⟩, hq⟩, (s⁻¹ * (hex.choose * a⁻¹))⁻¹,
    X'.Γ.inv_mem hsΓ, by group⟩
  show s⁻¹ * rep (f a) = s⁻¹ * hex.choose
  rw [hrep]

end GlobalTheory.HeckeEx.QFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyLiftsToLatticeMapScalingForms
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
open GlobalTheory.UnifPoint

noncomputable section

namespace GlobalTheory.HeckeLift

theorem int_eq_of_exp_eq_coprime {m n : ℤ} {p : ℕ} (hp : 0 < p)
    (h : ∀ k : ℕ, 0 < k → k.Coprime p → Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) : m = n := by
  set K : ℕ := 1 + (n - m).natAbs * p with hK
  have hk : 0 < K := by omega
  have hcop : K.Coprime p := by
    rw [hK]
    first
      | exact (Nat.coprime_add_mul_right_left 1 p _).2 (Nat.coprime_one_left p)
      | exact (Nat.coprime_add_mul_left_left 1 p _).2 (Nat.coprime_one_left p)
      | simp
  obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h K hk hcop)
  have h0 : ((K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have h1 : ((n - m : ℤ) : ℂ) = (((K : ℕ) : ℤ) * j : ℤ) := by
    apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_sub]
    generalize ((K : ℕ) : ℂ) = k at h0 hj
    field_simp at hj
    linear_combination (2 * Real.pi * Complex.I) * hj
  have hlt : (n - m).natAbs < K := by
    have : (n - m).natAbs ≤ (n - m).natAbs * p := Nat.le_mul_of_pos_right _ hp
    omega
  have h2 : n - m = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ⟨j, Int.cast_injective h1⟩ (by
    rw [Int.natAbs_natCast]; exact hlt)
  omega

theorem exists_linearMap_of_isHkIsog : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty) (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ)) (p : ℕ) (C : Subgroup (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (ψ : pullback Xo.univ.t.G.hom (F.u i P) ⟶ pullback Xo.univ.t.G.hom (F.u j P')) (ψp : (Over.mk (F.u i P) ⟶ Xo.univ.t.G) →* (Over.mk (F.u j P') ⟶ Xo.univ.t.G)), IsPeriod (F.Di i) ty P → IsPeriod (F.Di j) ty P' → p.Prime → (∀ a ∈ C, a ^ p ^ 2 = 1) → IsHkIsog p (F.u i P) (F.u j P') C ψ ψp → ∃ (gam : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, (F.Di j).EF (gam a) (gam b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧ (∀ b, ∃ a, gam a = (p ^ 2) • b) ∧ ∀ z, F.ex j P' (h z) = ψp (F.ex i P z) := by
  intro E _ _ _ H Dw l Xo σ g ty F i j P P' p C ψ ψp hP hP' hp hC hk
  obtain ⟨-, -, hfib, hact, hsurj, hker, hweil, -⟩ := hk
  obtain ⟨e, he⟩ : ∃ e : (Fin g → ℂ) → (Over.mk (F.u j P') ⟶ Xo.univ.t.G), ∀ z, e z = ψp (F.ex i P z) :=
    ⟨_, fun _ => rfl⟩
  have hpow : ∀ (n : ℕ) z, F.ex i P (n • z) = F.ex i P z ^ n := fun n z => by
    induction n with
    | zero => rw [zero_smul, pow_zero]; exact (F.ex_ker i P hP 0).2 ⟨0, map_zero P⟩
    | succ n ih => rw [succ_nsmul, F.ex_add i P hP, ih, pow_succ]
  have hp0 : 0 < p ^ 2 := pow_pos hp.pos 2
  have hkerC : ∀ z, e z = 1 → ∃ a, P a = (p ^ 2) • z := fun z hz => by
    have hmem : F.ex i P z ∈ C := by rw [← hker, MonoidHom.mem_ker, ← he, hz]
    obtain ⟨a, ha⟩ := (F.ex_ker i P hP _).1 ((hpow _ z).trans (hC _ hmem))
    exact ⟨a, ha⟩
  have hhol : IsHolTo Set.univ (fun z => (e z).left) := by
    have h1 := (GlobalTheory.HolFibre.isHolTo_fibPt_and_comp _ Xo.univ.t.G _ g (F.ex i P)
      (GlobalTheory.ClassUniq.isHolTo_ex F i P hP)).2 _ (ψ ≫ pullback.fst _ _)
    convert h1 using 2 with z
    rw [← Category.assoc, hfib, he]
    unfold fibPt
    exact (pullback.lift_fst _ _ _).symm
  have hc : {z | e z = 1}.Countable := by
    refine ((countable_periods hP).image fun w => ((p ^ 2 : ℕ) : ℂ)⁻¹ • w).mono fun z hz => ?_
    obtain ⟨a, ha⟩ := hkerC z hz
    refine ⟨P a, ⟨a, rfl⟩, ?_⟩
    have h0 : ((p ^ 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0.ne'
    simp only [ha, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ h0]
  have hexp : IsExp (F.ex j P') := ⟨F.ex_add j P' hP', F.ex_onto j P' hP', GlobalTheory.ClassUniq.isHolTo_ex F j P' hP',
    (F.ex_diff j P' hP').1, (F.ex_diff j P' hP').2⟩
  obtain ⟨h, hh⟩ := exists_linearEquiv_of_period hP' hexp (F.ex_ker j P' hP') (e₀ := e)
    (fun z w => by rw [he, he, he, F.ex_add i P hP, map_mul]) (fun y => by
      obtain ⟨z, hz⟩ := hsurj.comp (F.ex_onto i P hP) y
      exact ⟨z, (he z).trans hz⟩) hhol hc
  have hlin : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a := fun a z => by
    rw [he, he, F.ex_lin i P hP, hact]
  have hcomm : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := fun a z => by
    have := hP'.2.2.1
    have k := realLinear_eq_of_sub_mem_discrete (Γ := P'.range) DiscreteTopology.isDiscrete
      (L := (h.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.mulLeft ℝ (fun k => ty k (a : E)))
      (L' := LinearMap.mulLeft ℝ (fun k => ty k (a : E)) ∘ₗ (h.toLinearMap.restrictScalars ℝ)) fun x =>
        (F.ex_ker j P' hP' _).1 ((eq_iff_sub_of_add (F.ex_add j P' hP') _ _).1
          (((hh _).trans (hlin a x)).trans (by rw [← hh]; exact (F.ex_lin j P' hP' a (h x)).symm)))
    exact DFunLike.congr_fun k z
  have hmem : ∀ a, ∃ b, P' b = h (P a) := fun a =>
    (F.ex_ker j P' hP' _).1 ((hh _).trans (by rw [he, (F.ex_ker i P hP _).2 ⟨a, rfl⟩, map_one]))
  choose r₀ hr₀ using hmem
  let r₁ : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La :=
    { toFun := r₀
      map_add' := fun a b => hP'.2.1 (by rw [map_add, hr₀, hr₀, hr₀, map_add, map_add])
      map_smul' := fun c a => hP'.2.1 (by
        rw [hr₀, show P (c • a) = fun k => ty k (c : E) * P a k from funext (hP.1 c a), hcomm, ← hr₀]
        exact (funext (hP'.1 c (r₀ a))).symm) }
  refine ⟨r₁, h, fun a b => ?_, hr₀, fun b => ?_, fun z => (hh z).trans (he z)⟩
  · refine int_eq_of_exp_eq_coprime hp.pos fun k hk hcop => ?_
    have w := F.ex_weil i P hP k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have w1 := hweil k _ _ _ hcop w
    have w' := F.ex_weil j P' hP' k (r₀ a) (r₀ b) (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    rw [hr₀, hr₀, ← map_smul h, ← map_smul h, hh, hh, he, he] at w'
    have := congrArg Units.val (weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ (F.u j P') k _ _ _ _ w' w1)
    simp only [Units.val_mk0, Units.val_pow_eq_pow_val] at this
    rw [show r₁ a = r₀ a from rfl, show r₁ b = r₀ b from rfl, this, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  · obtain ⟨a, ha⟩ := hkerC (h.symm (P' b)) (by
      rw [← hh, h.apply_symm_apply]; exact (F.ex_ker j P' hP' _).2 ⟨b, rfl⟩)
    refine ⟨a, hP'.2.1 ?_⟩
    change P' (r₀ a) = _
    rw [hr₀, ha, map_nsmul, h.apply_symm_apply, map_nsmul]

end GlobalTheory.HeckeLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFrameExtensionOfRankZeroSignature
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.RankZeroFrames

open GlobalTheory.Models GlobalTheory.Models.RankZero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem exists_model_int (hD : Dw.p + Dw.q = 0) (Xo : Moduli Dw l) (c : Coeff l) :
    ∃ Y : Model Xo c (Int.castRingHom c.F), PushInvertible Y.t.G Y.t.PP.L := by
  obtain ⟨h₁, h₂⟩ := isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo
  let k := spMap (IntermediateField.inclusion c.le).toRingHom
  let β := Int.castRingHom c.F
  have hk : IsIso (pullback.snd Xo.s k) := inferInstance
  let j : Xo.XF c ⟶ pullback (𝟙 (Sp ℤ)) (spMap β) := pullback.snd Xo.s k ≫ inv (pullback.snd _ _)
  have hj : IsIso j := inferInstance
  have hs : Function.Surjective j := (inferInstance : Surjective j).1
  refine ⟨{ X := Sp ℤ, s := 𝟙 _, normal := ZJ.isNormalScheme_sp ℤ, proj := Inhab.isProjOver_id ℤ
            flat := inferInstance, jQ := j, jQ_over := (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (IsIso.inv_hom_id _)).trans (Category.comp_id _))
            jQ_open := inferInstance
            jQ_dense := hs.denseRange, t := Inhab.zeroTriple H _, oF := zeroObj hD l _
            m0 := (nonempty_objMap (isIso_zeroTriple _) h₂ _).some
            m := (nonempty_sabMap (isIso_zeroTriple _) (isIso_zeroTriple _) _).some
            ab_gen := by
              rw [hs.range_eq, Inhab.abLocus_eq_univ _ (Inhab.isProper_zeroTriple _), Set.preimage_univ] }, ?_⟩
  exact PushInv.pushInvertible_any GlobalTheory.allSixLaws.2.1.secBaseChangeAny GlobalTheory.allSixLaws.1.globalSectionsRank _
    (Out.Inh.zeroPolAV (Sp ℤ))

theorem intFrExt_of_rank_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.p + Dw.q = 0 → IntFrExt Xo c := by
  intro E _ _ _ H Dw l Xo c hD T io hfin x hx
  have hL := GlobalTheory.lawsFieldsSeparately
  have hB : Out.SecBaseChangeSt := hL.2.1
  have hT : Out.SecTwistSt := hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨Y, hPI⟩ := exists_model_int hD Xo c
  have hIF := GlobalTheory.intFrames_of_laws hB hT E H Dw l Xo c
  let _ := io.toAlgebra
  obtain ⟨y₀, -, h0, -, -⟩ := gfp_frPt_gen (Xo := Xo) (c := c) (L := T.Fr) (L' := T.Fr) hT (fun _ => rfl) x hx
    (fun _ i j => if i = j then 1 else 0) (fun _ _ => if_pos rfl) (fun _ _ _ h => if_neg h.ne')
  obtain ⟨y, t, hbor⟩ := intFr_of_model hIF T io Y hPI (Int.castRingHom T.V) (RingHom.ext_int _ _) y₀
  refine ⟨T, RingHom.id _, 1, one_pos, fun z => by simp, hfin, y, ?_⟩
  have h1 : y.1.x = y₀.x := hbor.1
  have h2 : spMap (RingHom.id T.Fr) = 𝟙 _ := Spec.map_id _
  show y.1.x = _
  rw [h2, Category.id_comp, h1, h0]

end GlobalTheory.RankZeroFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerContinuousRepresentativePowerBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjRepBound

set_option maxHeartbeats 1000000 in

theorem contRep_bound : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → 1 ≤ (D.sp.Y 0).rank → ∃ m : ℕ, ∀ u : (MP R).Vec, ∃ C : ℝ, ∀ y : X.B.I.GA, ‖GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) y‖ ≤ C * (GlobalTheory.Count.tau1 X.B.I y)⁻¹ ^ m := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h h1 h2 h3 hH hι t c ht hcl hc Φ hΦ hrep hrank
  classical
  have hn : 1 ≤ X.B.I.n := by
    rw [← GlobalTheory.Core.Mi.rank_eq X h]
    exact hrank
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hexp : ∀ τ, ∀ Y ∈ lieAt (D.sp.Y 0) τ, ∀ s : ℝ,
      NormedSpace.exp (s • Y) ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ) := fun τ Y hY s =>
    GlobalTheory.SmoothAutCheck.exp_mem_UH (Formalism.IndefR.Eqv.gramAt_isUnit D (D.sp.Y 0) τ) hY s
  obtain ⟨-, hfin, -, hpl, -⟩ := GlobalTheory.ConjRowAut.iota_data R.θ h3.inf hexp X.B.I h
  have hιt : (iotaX X h t).1 = 1 := hfin t ht
  have hcomm : ∀ z : X.B.I.GA, z.2 = 1 → iotaX X h t * z = z * iotaX X h t := by
    intro z hz
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_mul, hιt]
    · simp [Prod.snd_mul, hz]
  have hsymm : ∀ z, iotaX X h ((iotaX X h).toMulEquiv.symm z) = z := fun z =>
    (iotaX X h).toMulEquiv.apply_symm_apply z
  obtain ⟨f, hfdef⟩ : ∃ f : (MP R).Vec → X.B.I.GA → ℂ, ∀ u,
      f u = GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) :=
    ⟨_, fun _ => rfl⟩
  have hf : ∀ u, Formalism.L2.SG.EvalTOntoRep.IsContRep X
      (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) (f u) := by
    intro u
    obtain ⟨ψ, hψ⟩ := hrep u
    rw [hfdef, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
    exact hψ
  have hK : ∀ u, ∀ k ∈ X.B.I.Kg X.B.g, ∀ y, f u (y * (1, k)) = f u y := by
    intro u k hk y
    obtain ⟨S, -, hS⟩ := Submodule.mem_map.mp hΦ
    have hΦz : ∀ z, Φ z = X.B.Re (S z) := fun z => by rw [← hS]; rfl
    have hR : X.B.R (1, k) (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) =
        Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u)) := by
      rw [hΦz]
      exact ContinuousLinearMap.ext_iff.mp (GlobalTheory.Dec.CuspFrame.re_fixed X.B k hk) _
    have hr := Formalism.L2.SG.EvalTOntoRep.contRep_reg X (hf u) ((1, k) : X.B.I.GA)
    rw [hR] at hr
    exact congrFun (Formalism.L2.SG.EvalTOntoRep.contRep_unique X hr (hf u)) y
  have he := GlobalTheory.T.conjugatedIntertwiner_equivariant_realPlace hDS R F X h h1 h2 h3 hH hι t c ht hcl hc Φ hΦ hrep
  have hs := GlobalTheory.T.conjugateIntertwinerValues_sobolevContinuous hDS R F X h h1 h2 h3 hH hι t c ht hcl hc Φ hΦ hrep
  obtain ⟨m, hm⟩ := GlobalTheory.T.derivativeClosedClass_bounded_by_inverseLeastSize X.B hn hg
  have hW : ∀ g ∈ Set.range f, (∃ G, GlobalTheory.Dec.IsContRep X.B G g) ∧
      (∀ k ∈ X.B.I.Kg X.B.g, ∀ y, g (y * (1, k)) = g y) ∧
      ∀ (v : NumberField.InfinitePlace X.B.I.F) (E : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (X.B.I.ε v)), ∃ g' ∈ Set.range f,
        ∀ y, HasDerivAt (fun s : ℝ => g (y * GlobalTheory.SobolevBound.onePar X.B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace X.B v E) s))
          (g' y) 0 := by
    rintro _ ⟨u, rfl⟩
    refine ⟨⟨_, hf u⟩, hK u, fun v E => ?_⟩
    obtain ⟨τ, Y, hY, hYt⟩ := hpl v E.1 E.2
    have h2s : ∀ s : ℝ, (iotaX X h (oneP R.θ (D.sp.Y 0) τ Y s)).2 = 1 := fun s => (hYt s).1
    have hone : ∀ s : ℝ, iotaX X h (oneP R.θ (D.sp.Y 0) τ Y s) =
        GlobalTheory.SobolevBound.onePar X.B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace X.B v E) s := fun s =>
      GlobalTheory.RepSmooth.eq_onePar X.B v E s (hYt s).1 (hYt s).2.1 (hYt s).2.2
    refine ⟨f (Function.update u τ (GlobalTheory.RepSmooth.der u τ hY)), ⟨_, rfl⟩, fun y => ?_⟩
    have key := (GlobalTheory.RepSmooth.hasDerivAt_switch he hs τ u hY (iotaX X h).toMulEquiv
      (fun s => iotaX X h (oneP R.θ (D.sp.Y 0) τ Y s)) (fun _ => rfl) (y * iotaX X h t)).star
    have hfun : (fun s : ℝ => f u (y * GlobalTheory.SobolevBound.onePar X.B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace X.B v E) s)) =
        fun s => star (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u ((iotaX X h).toMulEquiv.symm
          (y * iotaX X h t * iotaX X h (oneP R.θ (D.sp.Y 0) τ Y s)))) := by
      funext s
      erw [GlobalTheory.ConjRowMult.conjMap_apply X (MP R) c Φ h t]
      rw [star_star, ← hone s, hfdef]
      congr 1
      erw [map_mul, map_inv, hsymm]
      rw [mul_assoc y, hcomm _ (h2s s), ← mul_assoc, mul_inv_cancel_right]
    have hval : f (Function.update u τ (GlobalTheory.RepSmooth.der u τ hY)) y =
        star (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t (Function.update u τ (GlobalTheory.RepSmooth.der u τ hY))
          ((iotaX X h).toMulEquiv.symm (y * iotaX X h t))) := by
      erw [GlobalTheory.ConjRowMult.conjMap_apply X (MP R) c Φ h t]
      rw [star_star]
      erw [map_mul, map_inv, hsymm]
      rw [mul_inv_cancel_right, hfdef]
    rw [hfun, hval]
    exact key
  refine ⟨m, fun u => ?_⟩
  have hb := hm (Set.range f) hW (f u) ⟨u, rfl⟩
  rw [hfdef] at hb
  exact hb

end GlobalTheory.ConjRepBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsProperModelOfExtendsFibreIsogeny
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

theorem isProper_of_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x x' : Sp T.Fr ⟶ Xo.X) (G G' : SAB H (Sp T.V)) (t t' : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr))) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (F : G.G ⟶ G'.G) (N : ℕ), Ext m₁ m₂ n₁ n₂ f F → f' ≫ f = 𝟙 _ ^ N → 0 < N → IsProper G.G.hom → IsProper G'.G.hom := by
  intro E _ _ _ H Dw l Xo T x x' G G' t t' m₁ m₂ n₁ n₂ f f' F N ⟨ψ, _, hψ, hc⟩ hN hpos hG
  have hU : IsAbelianScheme Xo.univ.t.G :=
    ⟨Xo.univ.t.semi.comm, Xo.univ.t.semi.smooth, Xo.univ.proper, Xo.univ.t.semi.geomConnected⟩
  have hA : IsAbelianScheme (Fib Xo x') := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback x' _ hU
  have hB : IsAbelianScheme G.G := ⟨G.semi.comm, G.semi.smooth, hG, G.semi.geomConnected⟩
  have hch : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)
  have hu : IsUnit (N : Γ(Sp T.Fr, ⊤)) := by
    have h0 : IsUnit (N : T.Fr) := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hpos.ne')
    have := h0.map (Scheme.ΓSpecIso (CommRingCat.of T.Fr)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨-, -, -, hs⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective _ (Fib Xo x') N hA hu
  have hl : f'.left ≫ f.left = (𝟙 (Fib Xo x') ^ N).left := congrArg (·.left) hN
  have hf : Function.Surjective f.left := by
    intro y
    obtain ⟨z, hz⟩ := hs.1 y
    refine ⟨f'.left z, ?_⟩
    rw [← Scheme.Hom.comp_apply, hl, hz]
  have p₁ : IsPullback m₁.φ t.G.hom Xo.univ.t.G.hom x := m₁.cart.1
  have q₁ : IsPullback n₁.φ t'.G.hom Xo.univ.t.G.hom x' := n₁.cart.1
  have q₂ : IsPullback n₂.φ t'.G.hom G'.G.hom (spMap (algebraMap T.V T.Fr)) := n₂.cart.1
  have hsq := hc p₁.isoPullback.hom q₁.isoPullback.hom (by simp) (by simp) (by simp) (by simp)
  have hψs : Function.Surjective ψ.left := by
    intro y
    obtain ⟨z, hz⟩ := hf (q₁.isoPullback.hom y)
    obtain ⟨w, rfl⟩ := (inferInstance : Surjective p₁.isoPullback.hom).1 z
    refine ⟨w, q₁.isoPullback.hom.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
    exact hz
  refine (GlobalTheory.isAbelianScheme_of_generically_surjective T.V T.Fr G.G G'.G hB G'.semi F ?_).proper
  rintro y ⟨s, hs⟩
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback q₂ y s hs.symm
  obtain ⟨w, rfl⟩ := hψs z
  refine ⟨m₂.φ w, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hψ, Scheme.Hom.comp_apply, hz]

end GlobalTheory.HkIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionNonsplitPlaceStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_decomposition_nonsplit_place : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (a : GL (Fin V.rank) (TensorProduct D.host.F (AF D.host.F) D.host.E)), Φ.IsGood D.sp.cm L a → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → ∀ (g : GLoc D.sp.cm.sig V.gram v), ∃ q k : GLoc D.sp.cm.sig V.gram v, k ∈ stabLoc D.sp.cm.sig V.gram L v ∧ g = q * k ∧ ∃ β : GL (Fin (wittIndex V)) (TensorProduct D.host.F (Fv D.host.F v) D.host.E), (HA.mat (F := D.host.F) (Fv D.host.F v) D.sp.cm.sig V.gram q).1 * (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) = (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) * β.1 := by
  first | exact @GlobalTheory.InertIwasawaLoc.eq_mul_stab_of_not_split | exact GlobalTheory.InertIwasawaLoc.eq_mul_stab_of_not_split | (intros; apply GlobalTheory.InertIwasawaLoc.eq_mul_stab_of_not_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanCoordinateActionSymplecticStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_archimedean_coordinate_action_symplectic : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (h : UA σ W.J)
    (v v' : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
    omega (trP F (Fin n × Fin d)) (archAct M h v) (archAct M h v') = omega (trP F (Fin n × Fin d)) v v' := by
  first | exact @GlobalTheory.ArchLine.omega_archAct | exact GlobalTheory.ArchLine.omega_archAct | (intros; apply GlobalTheory.ArchLine.omega_archAct <;> assumption)
end

