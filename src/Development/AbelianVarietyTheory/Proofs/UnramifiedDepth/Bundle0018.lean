import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0015
import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import ReciprocityTheory.DualLattices.Bundle0029
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.DualLattices.IsFibreSq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChainStepKernelRankLeModMaxIdealStatement
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainStep_kernel_rank_le_mod_maxIdeal : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ (i : ℕ) (S : Sys (X.G g)) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z (I g)), Adapted S D a i → ∀ s : ℕ, s + 1 < Formalism.BaseCaseIdentities.Kn i → ∀ (m : ℕ) (y : Fin m → I g → C), (∀ δ c, V.Ge 0 (y δ c)) → IndepMod V (fun δ c => if D.lev c = s then y δ c else 0) → ∀ (N : ℕ) (x : Fin N → Fin m → C), (∀ ν δ, V.Ge 0 (x ν δ)) → IndepMod V x → (∀ ν e, D.lev e = s + 1 → V.MM (∑ δ, x ν δ ^ (V.l ^ 2) * ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s), (V.l : C) * D.al c 2 e * y δ c ^ (V.l ^ 2))) → N ≤ X.j' := by
  first | exact @GlobalTheory.ChainStep.rank_le | exact GlobalTheory.ChainStep.rank_le | (intros; apply GlobalTheory.ChainStep.rank_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChartPSmulLiftEqBt
section
noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

section

variable {R₀ : Type} [CommRing R₀] {g : ℕ} {V : Type} [AddCommGroup V] [Module R₀ V]

private def btTanCrd (gb : Module.Basis (Fin g) R₀ V) (M : Type) [AddCommGroup M] [Module R₀ M]
    (k : Fin g) : V ⊗[R₀] M →ₗ[R₀] M :=
  (TensorProduct.lid R₀ M).toLinearMap ∘ₗ LinearMap.rTensor M (gb.coord k)

private lemma btTanCrd_tmul (gb : Module.Basis (Fin g) R₀ V) {M : Type} [AddCommGroup M]
    [Module R₀ M] (k : Fin g) (w : V) (m : M) :
    btTanCrd gb M k (w ⊗ₜ m) = gb.repr w k • m := by
  simp [btTanCrd]

private lemma btTanCrd_nat (gb : Module.Basis (Fin g) R₀ V) {M N : Type} [AddCommGroup M]
    [Module R₀ M] [AddCommGroup N] [Module R₀ N] (f : M →ₗ[R₀] N) (k : Fin g) (v : V ⊗[R₀] M) :
    btTanCrd gb N k (LinearMap.lTensor V f v) = f (btTanCrd gb M k v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul w m => simp [btTanCrd_tmul]
  | add x y hx hy => simp [hx, hy]

private lemma btTanCrd_base (gb : Module.Basis (Fin g) R₀ V) {S : Type} [CommRing S]
    [Algebra R₀ S] (k : Fin g) (v : V ⊗[R₀] S) :
    (Module.Basis.baseChange S gb).repr (TensorProduct.comm R₀ V S v) k = btTanCrd gb S k v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul w m => simp [btTanCrd_tmul]
  | add x y hx hy => simp [hx, hy]

end

private lemma btTan_chi_tg {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀}
    (ch : FormalChartAtZero B K g) {R S : LAlg R₀}
    (hF : ∀ a : Fin g → (R : Type), (∀ i, IsNilpotent (a i)) →
      ∃ M : Matrix (Fin g) (Fin g) (R : Type),
        (∀ k j, M k j - (1 : Matrix (Fin g) (Fin g) (R : Type)) k j ∈ Ideal.span (Set.range a)) ∧
        ∀ e : Fin g → (R : Type), (∀ i j, e i * e j = 0) → fAdd ch.F a e = a + M *ᵥ e)
    (ρ : LHom R K) (hρ : IsNilOver ρ) (π : LHom R S) (hπ : π.SqZero)
    (ρS : LHom S K) (hfac : ρS.comp π = ρ) (v : B.gg ⊗[R₀] π.ker) (k : Fin g) :
    ((ch.χ ρ hρ ⟨B.tg π hπ v, map_tg_ker B ρ π hπ ρS hfac _⟩ k : maximalIdeal (R : Type)) :
      (R : Type)) = (btTanCrd ch.gb π.ker k v : (R : Type)) := by
  have hmul : ∀ x ∈ RingHom.ker π.1, ∀ y ∈ RingHom.ker π.1, x * y = 0 := by
    intro x hx y hy
    have := Ideal.mul_mem_mul hx hy
    rw [← pow_two, hπ.2] at this
    exact this
  induction v using TensorProduct.induction_on generalizing k with
  | zero =>
    have := ch.χ_tg ρ hρ π hπ ρS hfac 0 0 k
    simpa using this
  | tmul w m =>
    rw [ch.χ_tg ρ hρ π hπ ρS hfac w m k, btTanCrd_tmul]; rfl
  | add x y hx hy =>
    have h := congrFun (ch.χ_add ρ hρ ⟨B.tg π hπ x, map_tg_ker B ρ π hπ ρS hfac _⟩
      ⟨B.tg π hπ y, map_tg_ker B ρ π hπ ρS hfac _⟩) k
    simp only [hx, hy] at h
    obtain ⟨M, hM, hMe⟩ := hF (fun k => (btTanCrd ch.gb π.ker k x : (R : Type)))
      (fun i => ⟨2, by rw [pow_two]; exact hmul _ (btTanCrd ch.gb π.ker i x).2 _ (btTanCrd ch.gb π.ker i x).2⟩)
    rw [hMe _ (fun i j => hmul _ (btTanCrd ch.gb π.ker i y).2 _ (btTanCrd ch.gb π.ker j y).2)] at h
    have hle : Ideal.span (Set.range fun k => (btTanCrd ch.gb π.ker k x : (R : Type))) ≤
        RingHom.ker π.1 := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (btTanCrd ch.gb π.ker i x).2
    have h0 : ((M - 1) *ᵥ fun k => (btTanCrd ch.gb π.ker k y : (R : Type))) k = 0 := by
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      exact hmul _ (hle (hM k j)) _ (btTanCrd ch.gb π.ker j y).2
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, sub_eq_zero] at h0
    rw [Pi.add_apply, h0] at h
    simp only [map_add, Submodule.coe_add]
    exact h

theorem chart_p_smul_lift_eq_bt :
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
    ∃ M : Matrix (Fin g) (Fin g) S, (∀ k j, M k j - (1 : Matrix (Fin g) (Fin g) S) k j ∈ Ideal.span (Set.range a)) ∧
      ∀ e : Fin g → S, (∀ i j, e i * e j = 0) → fAdd ch.F a e = a + M *ᵥ e) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), ∀ t : TT p g, ∃ t' : B.G D.wd.W,
    B.map D.wd.πW t' = B.map (Tw.q 0) (ptOf B D.L.τ (red p g t)) ∧
    ∃ h : B.map D.wd.ρW (p • t') = 0, ∀ k : Fin g, ∃ w : (D.wd.W : Type),
      D.wd.πW.1 w = (Tw.q 0).1 ((D.H.Bt *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k) ∧
      ((D.ch.χ D.wd.ρW D.sm.nil ⟨p • t', h⟩ k : maximalIdeal (D.wd.W : Type)) : (D.wd.W : Type)) = p * (D.wd.b : (D.wd.W : Type)) * w) := by
  intro hF R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D t
  choose th w hth hpth hw using fun i => D.L.bt_spec i 1
  have hsq : D.wd.πW.SqZero := D.wd.πW.sqZero_of_span (p : (D.wd.W : Type)) D.wd.πW_surj
    D.wd.ker_πW (by rw [← pow_two]; exact D.wd.p_sq)
  have hc1 : D.wd.πW.comp D.wd.ψ = (Tw.r 0).comp (Tw.π 1) :=
    Subtype.ext (AlgHom.ext fun a => D.wd.compat a)
  have hc2 : (Tw.r 0).comp (Tw.q 1) = Tw.q 0 :=
    Subtype.ext (AlgHom.ext fun a => Tw.r_q 0 a)
  have hf : ∀ a ∈ (Tw.π 1).ker, D.wd.ψ.1.toLinearMap a ∈ D.wd.πW.ker := by
    intro a ha
    change D.wd.πW.1 (D.wd.ψ.1 a) = 0
    change (Tw.π 1).1 a = 0 at ha
    rw [D.wd.compat, ha, map_zero]
  let n : Ix g → ℕ := fun i => (red p g t i).val
  let v : B.gg ⊗[R₀] D.wd.πW.ker := ∑ i, n i • LinearMap.lTensor B.gg
    (D.wd.ψ.1.toLinearMap.restrict hf)
    (TensorProduct.map LinearMap.id (ξmul (Tw.π 1) (Tw.ξ 1) (Tw.ξ_mem 1)) (w i))
  have hpt : p • ∑ i, n i • B.map D.wd.ψ (p • th i) = B.tg D.wd.πW hsq v := by
    simp only [v, map_sum, map_nsmul (B.tg D.wd.πW hsq), Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [B.tg_nat (Tw.π 1) D.wd.πW (Tw.sqZero 1) hsq, ← hpth, smul_comm p, ← map_nsmul,
      smul_smul, pow_two]
  refine ⟨∑ i, n i • B.map D.wd.ψ (p • th i), ?_, ?_⟩
  · simp only [ptOf, map_sum, map_nsmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← B.map_comp, hc1, B.map_comp, hth, ← B.map_comp, hc2, D.L.τ_compat i 0, map_nsmul]
  · refine ⟨hpt ▸ map_tg_ker B _ _ hsq _ D.wd.ρW_eq v, fun k => ?_⟩
    refine ⟨∑ i, n i • D.wd.ψ.1 (btTanCrd D.ch.gb _ k (w i)), ?_, ?_⟩
    · simp only [map_sum, map_nsmul, Matrix.mulVec, dotProduct, map_mul, Function.comp_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 := congrArg (btTanCrd D.ch.gb _ k) (hw i)
      rw [btTanCrd_nat, btTanCrd_nat] at h1
      simp only [AlgHom.toLinearMap_apply] at h1
      rw [D.wd.compat, h1, Tw.r_q, D.L.Bt_eq, btTanCrd_base]
      have h2 : (Tw.q 0).1 (algebraMap ℤ_[p] (Tw.O : Type) (t i)) = (n i : (Tw.R 0 : Type)) := by
        have h3 : t i - (n i : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
          rw [RingHom.mem_ker, map_sub, map_natCast]
          simp only [n, red]
          rw [ZMod.natCast_zmod_val, sub_self]
        rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h3
        obtain ⟨c, hc⟩ := h3
        have hp0 : (Tw.q 0).1 (p : (Tw.O : Type)) = 0 := by
          rw [← RingHom.mem_ker, D.tower_zero_ker]; exact Ideal.subset_span rfl
        rw [eq_add_of_sub_eq hc.symm]
        simp only [map_add, map_mul, map_natCast (algebraMap ℤ_[p] (Tw.O : Type)), hp0]
        simp
      rw [h2, nsmul_eq_mul, mul_comm]
    · have h := btTan_chi_tg D.ch (hF D.ch _) D.wd.ρW D.sm.nil D.wd.πW hsq D.wd.ρ1 D.wd.ρW_eq v k
      simp only [hpt]
      rw [h]
      simp only [v, map_sum, map_nsmul, AddSubmonoidClass.coe_finset_sum,
        AddSubmonoidClass.coe_nsmul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [btTanCrd_nat, ← LinearMap.lTensor_def, btTanCrd_nat, ← D.wd.ξ_img, mul_smul_comm,
        ← map_mul]
      congr 1

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffIntegralOnExponentsSubstOfLowerSetStatement
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffIntegralOnExponents_subst_of_lower_set : ∀ (C : Type) [Field C] (V : VF C) (σ τ : Type) [Fintype σ] [Fintype τ] (P : (σ →₀ ℕ) → Prop), (∀ μ ν, ν ≤ μ → P μ → P ν) → ∀ (γ : MvPowerSeries τ C) (T : τ → MvPowerSeries σ C), (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) → (∀ w, MvPowerSeries.constantCoeff (T w) = 0) → (∀ w μ, P μ → V.Ge 0 (MvPowerSeries.coeff μ (T w))) → ∀ μ, P μ → V.Ge 0 (MvPowerSeries.coeff μ (MvPowerSeries.subst T γ)) := by
  first | exact @GlobalTheory.LowerSubst.subst_int_on_lower | exact GlobalTheory.LowerSubst.subst_int_on_lower | (intros; apply GlobalTheory.LowerSubst.subst_int_on_lower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffLeafGaugeSubMainTermEqZeroOnFirstAxisStatement
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_leafGauge_sub_mainTerm_eq_zero_on_first_axis : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) (i : ℕ) (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C) (Φ : ι' → ι → C) (μ : ι ⊕ ι' →₀ ℕ), (∀ b, μ (Sum.inr b) = 0) → MvPowerSeries.coeff μ (X.hM g a i e v' - mainM V i Φ) = 0 := by
  first | exact @GlobalTheory.MainTerm.Axis.coeff_hM_sub_mainM_eq_zero | exact GlobalTheory.MainTerm.Axis.coeff_hM_sub_mainM_eq_zero | (intros; apply GlobalTheory.MainTerm.Axis.coeff_hM_sub_mainM_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DualTowerMapExists
section
noncomputable section

namespace GlobalTheory

section Helpers

open ReciprocityTheory.PGsh

private def dualTowerRing {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S) (ψ : LHom Λ S) :
    DualNum.DN Λ →+* (Dq.D : Type) :=
  Ideal.Quotient.lift _
    (Polynomial.eval₂RingHom ((Dq.σ.1.comp ψ.1 : (Λ : Type) →ₐ[R₀] (Dq.D : Type)) :
      (Λ : Type) →+* (Dq.D : Type)) Dq.η) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, sq, Dq.η_sq, mul_zero])

private lemma dualTowerRing_C {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) (r : (Λ : Type)) :
    dualTowerRing Dq ψ (Ideal.Quotient.mk _ (Polynomial.C r)) = Dq.σ.1 (ψ.1 r) := by
  rw [dualTowerRing, Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  rfl

private lemma dualTowerRing_X {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) : dualTowerRing Dq ψ (DualNum.eta Λ) = Dq.η := by
  rw [dualTowerRing, DualNum.eta, Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X]

private lemma dualTowerRing_π {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) (x : DualNum.DN Λ) :
    Dq.π.1 (dualTowerRing Dq ψ x) = ψ.1 (DualNum.ev Λ x) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction f using Polynomial.induction_on with
  | C a => rw [dualTowerRing_C, Dq.sect, DualNum.ev_mk, Polynomial.eval_C]
  | add f g hf hg => simp only [map_add, hf, hg]
  | monomial n a _ =>
    have h := dualTowerRing_X Dq ψ
    rw [DualNum.eta] at h
    rw [DualNum.ev_mk, pow_succ Polynomial.X n, ← mul_assoc, map_mul, map_mul, h, map_mul, Dq.π_η]
    simp

private lemma dualTower_map_exists {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) :
    ∃ f : LHom (DualNum.dualPair Λ).D Dq.D,
      (∀ x, Dq.π.1 (f.1 x) = ψ.1 ((DualNum.dualPair Λ).π.1 x)) ∧
      (∀ x, f.1 ((DualNum.dualPair Λ).σ.1 x) = Dq.σ.1 (ψ.1 x)) ∧
      f.1 (DualNum.dualPair Λ).η = Dq.η := by
  let fA : DualNum.DN Λ →ₐ[R₀] (Dq.D : Type) :=
    { dualTowerRing Dq ψ with
      commutes' := fun r => by
        show dualTowerRing Dq ψ (algebraMap R₀ (DualNum.DN Λ) r) = _
        rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply, dualTowerRing_C,
          AlgHom.commutes, AlgHom.commutes] }
  refine ⟨mkLHom (R := (DualNum.dualPair Λ).D) fA fun a ha => ?_, fun x => dualTowerRing_π Dq ψ x,
    fun x => ?_, dualTowerRing_X Dq ψ⟩
  · refine (DualNum.dualPair Λ).isUnit_of_π ?_
    have h1 : IsUnit (Dq.π.1 (dualTowerRing Dq ψ a)) := ha.map Dq.π.1
    exact ψ.2.map_nonunit _ ((dualTowerRing_π Dq ψ a) ▸ h1)
  · show dualTowerRing Dq ψ (algebraMap (Λ : Type) (DualNum.DN Λ) x) = _
    rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply, dualTowerRing_C]
    rfl

private lemma dualTower_nonempty {R₀ : Type} [CommRing R₀] {p : ℕ} (Tw : ATowerL R₀ p) :
    Nonempty (DualTower Tw) := by
  choose d h₁ h₂ h₃ using fun n => dualTower_map_exists (DualNum.dualPair (Tw.R n)) (Tw.r n)
  exact ⟨⟨fun n => DualNum.dualPair (Tw.R n), d, h₁, h₂, h₃⟩⟩

end Helpers

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_dualTower :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} (Tw : ATowerL R₀ p), Nonempty (DualTower Tw)) :=
  fun Tw => dualTower_nonempty Tw

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvBtOfTangentOfSeries
section
noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

namespace BtAssembly

variable {R₀ : Type} [CommRing R₀]

private lemma chi_congr {B : BX R₀} {K : LAlg R₀} {g : ℕ} (ch : FormalChartAtZero B K g) {R : LAlg R₀}
    (ρ : LHom R K) (hρ : IsNilOver ρ) {x y : B.G R} (hx : B.map ρ x = 0) (hy : B.map ρ y = 0)
    (h : x = y) : ch.χ ρ hρ ⟨x, hx⟩ = ch.χ ρ hρ ⟨y, hy⟩ := by
  subst h; rfl

private lemma chi_zero {B : BX R₀} {K : LAlg R₀} {g : ℕ} (ch : FormalChartAtZero B K g) {R : LAlg R₀}
    (ρ : LHom R K) (hρ : IsNilOver ρ) (h0 : B.map ρ 0 = 0) (k : Fin g) :
    ((ch.χ ρ hρ ⟨0, h0⟩ k : maximalIdeal (R : Type)) : (R : Type)) = 0 := by
  have hsq : (LHom.id R).SqZero := by
    refine ⟨fun a => ⟨a, rfl⟩, ?_⟩
    have : RingHom.ker (LHom.id R).1 = ⊥ := by
      ext a; simp [RingHom.mem_ker, LHom.id]
    rw [this]; simp
  have h := ch.χ_tg ρ hρ (LHom.id R) hsq ρ rfl 0 0 k
  rw [chi_congr ch ρ hρ _ h0 (by simp)] at h
  simpa using h

private lemma chi_nsmul {B : BX R₀} {K : LAlg R₀} {g : ℕ} (ch : FormalChartAtZero B K g) {R : LAlg R₀}
    (ρ : LHom R K) (hρ : IsNilOver ρ) (x : B.G R) (hx : B.map ρ x = 0) (n : ℕ)
    (hn : B.map ρ (n • x) = 0) :
    (fun k => ((ch.χ ρ hρ ⟨n • x, hn⟩ k : maximalIdeal (R : Type)) : (R : Type))) =
      nsmulF ch.F (fun k => ((ch.χ ρ hρ ⟨x, hx⟩ k : maximalIdeal (R : Type)) : (R : Type))) n := by
  induction n with
  | zero =>
    funext k
    rw [chi_congr ch ρ hρ hn (map_zero _) (zero_nsmul x), chi_zero]
    rfl
  | succ n ih =>
    have hn' : B.map ρ (n • x) = 0 := by rw [map_nsmul, hx, nsmul_zero]
    have h := ch.χ_add ρ hρ ⟨n • x, hn'⟩ ⟨x, hx⟩
    rw [ih hn'] at h
    rw [chi_congr ch ρ hρ hn (map_add_ker B ρ ⟨n • x, hn'⟩ ⟨x, hx⟩) (succ_nsmul x n)]
    exact h

private lemma nil_of_mem {R K : LAlg R₀} (ρ : LHom R K) (hρ : IsNilOver ρ)
    (hK : maximalIdeal (K : Type) = ⊥) (a : maximalIdeal (R : Type)) :
    IsNilpotent (a : (R : Type)) := by
  apply hρ.2
  rw [RingHom.mem_ker]
  have : ρ.1 a ∈ maximalIdeal (K : Type) := fun hu => a.2 (ρ.2.map_nonunit _ hu)
  rw [hK] at this
  exact this

private lemma exists_pow_zero {S : Type} [CommRing S] {g : ℕ} (Y : Fin g → S)
    (h : ∀ l, IsNilpotent (Y l)) : ∃ N : ℕ, ∀ l, Y l ^ N = 0 := by
  choose n hn using h
  refine ⟨∑ l, n l, fun l => pow_eq_zero_of_le ?_ (hn l)⟩
  exact Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

private lemma comp_app {R S T : LAlg R₀} (f : LHom R S) (f' : LHom S T) (e : LHom R T)
    (h : f'.comp f = e) (a : (R : Type)) : f'.1 (f.1 a) = e.1 a := by
  subst h; rfl

end BtAssembly

open BtAssembly in

theorem evBt_of_tangent_of_series :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), ∀ t : TT p g, ∃ t' : B.G D.wd.W,
    B.map D.wd.πW t' = B.map (Tw.q 0) (ptOf B D.L.τ (red p g t)) ∧
    ∃ h : B.map D.wd.ρW (p • t') = 0, ∀ k : Fin g, ∃ w : (D.wd.W : Type),
      D.wd.πW.1 w = (Tw.q 0).1 ((D.H.Bt *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k) ∧
      ((D.ch.χ D.wd.ρW D.sm.nil ⟨p • t', h⟩ k : maximalIdeal (D.wd.W : Type)) : (D.wd.W : Type)) = p * (D.wd.b : (D.wd.W : Type)) * w) →
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (W : Type) [CommRing W] [Algebra R₀ W] (c : Fin g → W),
    (∀ i, IsNilpotent (c i)) → ∀ N : ℕ, ∃ Γ : Fin g → MvPolynomial (Fin g) W,
      (∀ k m, (∃ i, ¬ p ∣ m i) → MvPolynomial.coeff m (Γ k) ∈ Ideal.span {(p : W)}) ∧
      ∀ y : Fin g → W, (∀ i, y i ^ N = 0) → fAdd ch.F c (nsmulF ch.F y p) = fun k => MvPolynomial.eval y (Γ k)) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), 0 < g → maximalIdeal (D.K : Type) = ⊥ ∧ IsNilOver D.wd.ρ1 ∧ ∀ i : D.fin.ι,
    ∃ (Λ : LAlg R₀) (μ : LHom (D.fin.AAx i) Λ) (j : LHom (Tw.R 0) Λ) (ρΛ : LHom Λ D.K),
      IsNilOver ρΛ ∧ Function.Surjective μ.1 ∧ ρΛ.comp j = D.wd.ρ1 ∧ μ.comp (D.fin.sO i) = j.comp (Tw.q 0) ∧
      ∀ φ : LHom (D.fin.AAx i) Tw.O, φ.comp (D.fin.sO i) = LHom.id Tw.O →
        ∃ ψ : LHom Λ (Tw.R 0), ψ.comp μ = (Tw.q 0).comp φ ∧ ψ.comp j = LHom.id (Tw.R 0) ∧ D.wd.ρ1.comp ψ = ρΛ) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {Tw : ATowerL R₀ p} {K : LAlg R₀} (wd : WData Tw K) (g : ℕ), WFrobStatement wd g) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), EvBtStatement D) := by
  intro hTAN hGAM hLAM hWF R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D C _ _ k
  obtain ⟨hK, hρ1, hL⟩ := hLAM D (Fin.pos k)
  have key : ∀ i : D.fin.ι, ∃ F : (D.fin.AAx i : Type), ∀ φ : LHom (D.fin.AAx i) Tw.O,
      φ.comp (D.fin.sO i) = LHom.id Tw.O → ∀ t : TT p g,
      B.map φ (D.fin.y i) = ptOf B D.L.τ (red p g t) →
      (Tw.q 0).1 ((D.H.Bt *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k) = (Tw.q 0).1 (φ.1 F) := by
    intro i
    obtain ⟨Λ, μ, j, ρΛ, hΛ, hμ, hj, -, hψ⟩ := hL i
    obtain ⟨x, hx⟩ := D.sm.onto (B.map ρΛ (B.map μ (D.fin.y i)))
    have hc : B.map D.wd.ρW (p • x) = 0 := by
      rw [map_nsmul, hx, ← map_nsmul, ← map_nsmul, D.fin.y_p, map_zero, map_zero]
    have hz : B.map ρΛ (B.map μ (D.fin.y i) - B.map j (B.map D.wd.πW x)) = 0 := by
      rw [map_sub, ← B.map_comp j ρΛ, hj, ← B.map_comp D.wd.πW, D.wd.ρW_eq, hx, sub_self]
    obtain ⟨N, hN⟩ := exists_pow_zero
      (fun l => ((D.ch.χ ρΛ hΛ ⟨_, hz⟩ l : maximalIdeal (Λ : Type)) : (Λ : Type)))
      (fun l => nil_of_mem ρΛ hΛ hK _)
    obtain ⟨Γ, hΓ, hΓe⟩ := hGAM p D.ch (D.wd.W : Type)
      (fun l => ((D.ch.χ D.wd.ρW D.sm.nil ⟨_, hc⟩ l : maximalIdeal (D.wd.W : Type)) : (D.wd.W : Type)))
      (fun l => nil_of_mem D.wd.ρW D.sm.nil hK _) (N * 2)
    obtain ⟨Q, hQ⟩ := hWF D.wd g (Γ k) (hΓ k)
    obtain ⟨F, hF⟩ := hμ (j.1 (D.wd.πW.1 ((D.wd.b⁻¹ : (D.wd.W : Type)ˣ) : (D.wd.W : Type))) *
      MvPolynomial.eval₂ (j.1 : (Tw.R 0 : Type) →+* (Λ : Type))
        (fun l => ((D.ch.χ ρΛ hΛ ⟨_, hz⟩ l : maximalIdeal (Λ : Type)) : (Λ : Type))) Q)
    refine ⟨F, fun φ hφ t ht => ?_⟩
    obtain ⟨ψ, hψμ, hψj, hψρ⟩ := hψ φ hφ
    obtain ⟨t', ht', h, hw⟩ := hTAN D t
    obtain ⟨w, hw1, hw2⟩ := hw k
    have e1 : B.map D.wd.πW t' = B.map ψ (B.map μ (D.fin.y i)) := by
      rw [ht', ← ht, ← B.map_comp, ← B.map_comp, hψμ]
    have hu : B.map D.wd.ρW (t' - x) = 0 := by
      rw [map_sub, hx, ← D.wd.ρW_eq, B.map_comp, e1, ← B.map_comp ψ, hψρ, sub_self]
    have e2 : B.map D.wd.πW (t' - x) =
        B.map ψ (B.map μ (D.fin.y i) - B.map j (B.map D.wd.πW x)) := by
      rw [map_sub, map_sub, e1, ← B.map_comp j ψ, hψj, B.map_id]
    have e3 : ∀ l, D.wd.πW.1
        ((D.ch.χ D.wd.ρW D.sm.nil ⟨_, hu⟩ l : maximalIdeal (D.wd.W : Type)) : (D.wd.W : Type)) =
        ψ.1 ((D.ch.χ ρΛ hΛ ⟨_, hz⟩ l : maximalIdeal (Λ : Type)) : (Λ : Type)) := by
      intro l
      rw [← D.ch.χ_nat D.wd.ρW D.wd.ρ1 D.sm.nil hρ1 D.wd.πW D.wd.ρW_eq ⟨_, hu⟩ l,
        ← D.ch.χ_nat ρΛ D.wd.ρ1 hΛ hρ1 ψ hψρ ⟨_, hz⟩ l]
      rw [chi_congr D.ch D.wd.ρ1 hρ1 _ _ e2]
    have e4 : ∀ l, ((D.ch.χ D.wd.ρW D.sm.nil ⟨_, hu⟩ l : maximalIdeal (D.wd.W : Type)) :
        (D.wd.W : Type)) ^ (N * 2) = 0 := by
      intro l
      have : ((D.ch.χ D.wd.ρW D.sm.nil ⟨_, hu⟩ l : maximalIdeal (D.wd.W : Type)) :
          (D.wd.W : Type)) ^ N ∈ RingHom.ker D.wd.πW.1 := by
        rw [RingHom.mem_ker, map_pow, e3, ← map_pow, hN, map_zero]
      rw [D.wd.ker_πW, Ideal.mem_span_singleton'] at this
      obtain ⟨a, ha⟩ := this
      rw [pow_mul, ← ha, mul_pow, D.wd.p_sq, mul_zero]
    have hpu : B.map D.wd.ρW (p • (t' - x)) = 0 := by rw [map_nsmul, hu, nsmul_zero]
    have e5 := D.ch.χ_add D.wd.ρW D.sm.nil ⟨_, hc⟩ ⟨_, hpu⟩
    rw [chi_nsmul D.ch D.wd.ρW D.sm.nil _ hu p hpu, hΓe _ e4,
      chi_congr D.ch D.wd.ρW D.sm.nil _ h
        (show p • x + p • (t' - x) = p • t' by rw [← nsmul_add, add_sub_cancel])] at e5
    have e6 := congrFun e5 k
    rw [hw2] at e6
    obtain ⟨a, ha⟩ := D.wd.πW_surj (MvPolynomial.eval (fun l => D.wd.πW.1
      ((D.ch.χ D.wd.ρW D.sm.nil ⟨_, hu⟩ l : maximalIdeal (D.wd.W : Type)) : (D.wd.W : Type))) Q)
    have e7 := hQ _ (by
      rw [← e6, mul_assoc]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)) a ha
    rw [← e6] at e7
    have e8 : D.wd.πW.1 ((D.wd.b : (D.wd.W : Type)) * w - a) = 0 := by
      rw [← D.wd.ann_p, mul_sub, ← mul_assoc, e7, sub_self]
    rw [map_sub, sub_eq_zero] at e8
    have e9 : ψ.1 (MvPolynomial.eval₂ (j.1 : (Tw.R 0 : Type) →+* (Λ : Type))
        (fun l => ((D.ch.χ ρΛ hΛ ⟨_, hz⟩ l : maximalIdeal (Λ : Type)) : (Λ : Type))) Q) =
        D.wd.πW.1 a := by
      rw [ha]
      have hid : (ψ.1 : (Λ : Type) →+* (Tw.R 0 : Type)).comp
          (j.1 : (Tw.R 0 : Type) →+* (Λ : Type)) = RingHom.id _ :=
        RingHom.ext fun b => comp_app j ψ _ hψj b
      have := MvPolynomial.eval₂_comp_left (ψ.1 : (Λ : Type) →+* (Tw.R 0 : Type))
        (j.1 : (Tw.R 0 : Type) →+* (Λ : Type))
        (fun l => ((D.ch.χ ρΛ hΛ ⟨_, hz⟩ l : maximalIdeal (Λ : Type)) : (Λ : Type))) Q
      rw [hid] at this
      refine this.trans ?_
      rw [MvPolynomial.eval₂_id]
      congr 2
      funext l
      exact (e3 l).symm
    have e10 : (Tw.q 0).1 (φ.1 F) = ψ.1 (μ.1 F) := (comp_app μ ψ _ hψμ F).symm
    rw [e10, hF, map_mul, e9, comp_app j ψ _ hψj, ← hw1, ← e8]
    change _ = D.wd.πW.1 _ * _
    rw [← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
  choose F hF using key
  refine ⟨D.evAll C F, Submodule.subset_span ⟨F, rfl⟩, fun t => ?_⟩
  have hs := Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ (red p g t)) (D.pt_p (red p g t))))
  have h := hF (D.ptIdx (red p g t)) (D.ptMap (red p g t)) hs.1 t hs.2.1
  have hm : (D.H.Bt *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k -
      (D.ptMap (red p g t)).1 (F (D.ptIdx (red p g t))) ∈ RingHom.ker (Tw.q 0).1 := by
    rw [RingHom.mem_ker, map_sub, h, sub_self]
  rw [D.tower_zero_ker, Ideal.mem_span_singleton'] at hm
  obtain ⟨r, hr⟩ := hm
  refine ⟨r, ?_⟩
  rw [mul_comm, hr, map_sub]
  rfl

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsUnimodularMulEqNegOfIndependentModMaximalStatement
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unimodular_mul_eq_neg_of_independent_mod_maximal : ∀ (C : Type) [Field C] (V : VF C) (n n0 : ℕ) (Φ : Fin n → Fin n0 → C), (∀ b c, V.Ge 0 (Φ b c)) → IndepMod V (fun c b => Φ b c) → n0 ≤ n ∧ ∃ Y : Matrix (Fin n) (Fin n) C, (∀ b b', V.Ge 0 (Y b b')) ∧ V.v Y.det = 0 ∧ ∀ (b : Fin n) (c : Fin n0), b.val < n0 → ∑ b', Y b b' * Φ b' c = if b.val = c.val then -1 else 0 := by
  first | exact @GlobalTheory.exists_unimodular_mul_eq_neg_of_indepMod | exact GlobalTheory.exists_unimodular_mul_eq_neg_of_indepMod | (intros; apply GlobalTheory.exists_unimodular_mul_eq_neg_of_indepMod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HPullWUpGTwoGroupEmbeddingEqRenameStatement
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hPullW_upG_twoGroupEmbedding_eq_rename : ∀ (C : Type) [Field C] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (g : Fin 2) (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C), (∀ F : MvPowerSeries (I g) C, hPullW (upG g F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = MvPowerSeries.rename Sum.inl (linPull e F)) ∧ ∀ F : MvPowerSeries (I (1 - g)) C, hPullW (upG (1 - g) F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = MvPowerSeries.rename Sum.inr (linPull v' F) := by
  first | exact @GlobalTheory.MainTerm.hPullW_upG_toW | exact GlobalTheory.MainTerm.hPullW_upG_toW | (intros; apply GlobalTheory.MainTerm.hPullW_upG_toW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IndependentModFirstCoeffChainLastStepStatement
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.independentMod_firstCoeff_chainLastStep : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ (i : ℕ) (S : Sys (X.G g)) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z (I g)), Adapted S D a i → ∀ s : ℕ, s < Formalism.BaseCaseIdentities.Kn i → ∀ (m : ℕ) (y : Fin m → I g → C), (∀ δ c, V.Ge 0 (y δ c)) → IndepMod V (fun δ c => if D.lev c = s then y δ c else 0) → IndepMod V (fun δ (κ : J g) => ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s), y δ c ^ V.l * ((V.l : C) * S.be c 1 κ)) := by
  first | exact @GlobalTheory.LastStep.indepMod_first_coeff | exact GlobalTheory.LastStep.indepMod_first_coeff | (intros; apply GlobalTheory.LastStep.indepMod_first_coeff <;> assumption)
end

