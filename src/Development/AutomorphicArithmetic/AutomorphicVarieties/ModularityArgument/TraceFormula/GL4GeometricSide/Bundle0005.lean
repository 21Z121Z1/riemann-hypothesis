import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0795
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0578
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0574
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0789
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0564
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.ContOfRightInv
section
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.CompanionTheory.TwY PositivityTheory.RgBcC.Bridge

noncomputable section

namespace UpperTheory.V.Z.GSp4Splitting

private theorem cont_of_right_inv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K : Subgroup G}
    (hK : IsOpen (K : Set G)) {f : G → ℂ} (hf : ∀ g, ∀ k ∈ K, f (g * k) = f g) : Continuous f := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq f).2 fun g => ?_)
  have ho : IsOpen {y : G | g⁻¹ * y ∈ K} := hK.preimage (continuous_const.mul continuous_id)
  filter_upwards [ho.mem_nhds (show g⁻¹ * g ∈ K by simp)] with y hy
  rw [← hf g _ hy, mul_inv_cancel_left]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private def Fx (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) : Submodule ℂ π.V where
  carrier := {ψ | ∀ k ∈ K, finRep E n k ψ.1 = ψ.1}
  add_mem' {a b} ha hb k hk := by rw [Submodule.coe_add, map_add, ha k hk, hb k hk]
  zero_mem' k _ := map_zero _
  smul_mem' c a ha k hk := by rw [Submodule.coe_smul, map_smul, ha k hk]

private def res (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (T : Module.End ℂ (Sm E n)) (h1 : T ∈ stabAlg π)
    (h2 : ∀ k, Commute T (finRep E n k)) : Module.End ℂ (Fx π K) :=
  (T.restrict (p := π.V) (q := π.V) h1).restrict fun ψ hψ k hk => by
    change finRep E n k (T ψ.1) = T ψ.1
    rw [← Module.End.mul_apply, ← (h2 k).eq, Module.End.mul_apply, hψ k hk]

private theorem eopW_comm (w : InfinitePlace E) (s : Bool) (a b : Fin n) (k : GL (Fin n) (Af E)) :
    Commute (eopW w s a b) (finRep E n k) := by
  have h : ∀ i j x, Commute (lieS E n i j x) (finRep E n k) := fun i j x => lie_rt_fin _ k
  have h' : ∀ τ : E →+* ℂ, Commute (Eop τ a b) (finRep E n k) := fun τ =>
    ((h a b _).sub_left ((h a b _).smul_left _)).smul_left _
  cases s
  · exact h' _
  · exact h' _

private theorem sV_mem (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (w : InfinitePlace E) (c : Un n) :
    ∀ ψ ∈ Fx π K, sV π w c ψ ∈ Fx π K := fun ψ hψ k hk => by
  change rt E n (finGL E n k) (rt E n (infGL E n (locInf w (Unitary.toUnits c))) ψ.1) =
    rt E n (infGL E n (locInf w (Unitary.toUnits c))) ψ.1
  rw [← Module.End.mul_apply, ← map_mul, ← infGL_comm, map_mul, Module.End.mul_apply]
  exact congrArg _ (hψ k hk)

private def sF (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (w : InfinitePlace E) :
    Un n →* Module.End ℂ (Fx π K) where
  toFun c := (sV π w c).restrict (sV_mem π K w c)
  map_one' := LinearMap.ext fun ψ => Subtype.ext (by simp)
  map_mul' a b := LinearMap.ext fun ψ => Subtype.ext (by simp)

private theorem along_unit (w : InfinitePlace E) (g : GA E n) (φ : GA E n → ℂ) (c : Un n) :
    along w g φ c.1 = φ (g * kAt w c) := by
  have e : atW w c.1 = toL (locInf w (Unitary.toUnits c)).val := by
    funext i j v
    exact (locInf_apply w (Unitary.toUnits c) i j v).symm
  rw [along, e, chart_val]
  rfl

private theorem fix_apply {π : CuspSub E n} {K : Subgroup (GL (Fin n) (Af E))} {ψ : π.V} (hψ : ψ ∈ Fx π K)
    {k : GL (Fin n) (Af E)} (hk : k ∈ K) (x : GA E n) : ψ.1.1 (x * finGL E n k) = ψ.1.1 x :=
  (rt_apply (finGL E n k) x ψ.1).symm.trans (congrArg (fun φ : Sm E n => φ.1 x) (hψ k hk))

private theorem thV_mem (π : CuspSub E n) (hθ : ThetaFix π) (K : Subgroup (GL (Fin n) (Af E)))
    (hK : ∀ k ∈ K, thetaF E n k ∈ K) : ∀ ψ ∈ Fx π K, ThInv.thV π hθ ψ ∈ Fx π K := fun ψ hψ k hk =>
  Subtype.ext <| funext fun x => by
    refine (rt_apply (finGL E n k) x _).trans ?_
    rw [ThInv.thV_apply, ThInv.thV_apply, map_mul, ThInv.thetaA_finGL, fix_apply hψ (hK k hk)]

private theorem hecke_ex (hM : HeckeMem) (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E)))
    (ho : IsOpen (K : Set (GL (Fin n) (Af E)))) (hc : IsCompact (K : Set (GL (Fin n) (Af E))))
    [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))] (μf : Measure (GL (Fin n) (Af E)))
    [μf.IsHaarMeasure] (h : {h : GL (Fin n) (Af E) → ℂ // IsHeckeF K h}) :
    ∃ R : Module.End ℂ (Fx π K), ∀ u, (R u).1.1.1 = heckeOp μf h.1 u.1.1.1 := by
  have ex : ∀ u : Fx π K, ∃ v : Fx π K, v.1.1.1 = heckeOp μf h.1 u.1.1.1 := fun u => by
    obtain ⟨_, _, ψ', -, h1, h2⟩ := hM E n π K ho hc μf h.1 h.2 u.1
    exact ⟨⟨ψ', h2⟩, h1⟩
  choose r hr using ex
  have hint : ∀ (u : Fx π K) (x : GA E n), Integrable (fun g => h.1 g * u.1.1.1 (x * finGL E n g)) μf := fun u x => by
    refine Continuous.integrable_of_hasCompactSupport (cont_of_right_inv ho fun g k hk => ?_) h.2.1.mul_right
    have e := h.2.2 1 K.one_mem k hk g
    rw [one_mul] at e
    rw [e, map_mul, ← mul_assoc, fix_apply u.2 hk]
  refine ⟨{ toFun := r, map_add' := fun a b => ?_, map_smul' := fun c a => ?_ }, hr⟩ <;>
    refine Subtype.ext <| Subtype.ext <| Subtype.ext <| funext fun x => ?_
  · change (r (a + b)).1.1.1 x = (r a).1.1.1 x + (r b).1.1.1 x
    rw [hr, hr, hr, heckeOp, heckeOp, heckeOp, ← integral_add (hint a x) (hint b x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact mul_add _ _ _
  · change (r (c • a)).1.1.1 x = c * (r a).1.1.1 x
    rw [hr, hr, heckeOp, heckeOp, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact mul_left_comm _ _ _

@[reducible] private def core (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ)
    (hH : IsPet π H) : InnerProductSpace.Core ℂ (Fx π K) where
  inner x y := H x.1 y.1
  conj_inner_symm x y := hH.1 _ _
  re_inner_nonneg x := by
    by_cases hx : x.1 = 0
    · simp [hx]
    · exact (hH.2.1 _ hx).le
  add_left x y z := by simp
  smul_left x y c := by simp
  definite x hx := by
    by_contra h0
    have := hH.2.1 x.1 fun e => h0 (Subtype.ext e)
    have hx' : H x.1 x.1 = 0 := hx
    simp [hx'] at this

end UpperTheory.V.Z.GSp4Splitting

theorem UpperTheory.V.Z.GSp4Splitting.rlEx :
    PetEx → HeckeMem → RlEx := by
  intro hP hM E _ _ _ n hn π hθ K ho hc hK _ _ μf _
  obtain ⟨H, hH⟩ := hP E n hn π hθ
  choose R hR using hecke_ex hM π K ho hc μf
  letI c : InnerProductSpace.Core ℂ (Fx π K) := core π K H hH
  exact ⟨{
    U := Fx π K
    nacg := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
    ips := InnerProductSpace.ofCore c.toCore
    i := (Fx π K).subtype
    inj := Subtype.val_injective
    rng := fun ψ => ⟨fun ⟨u, hu⟩ => hu ▸ u.2, fun h => ⟨⟨ψ, h⟩, rfl⟩⟩
    H := H
    pet := hH
    inner_eq := fun _ _ => rfl
    E1 := fun w a b => res π K _ (eopW_mem_stabAlg π w true a b) (eopW_comm w true a b)
    E2 := fun w a b => -res π K _ (eopW_mem_stabAlg π w false b a) (eopW_comm w false b a)
    σ := sF π K
    Θ := (ThInv.thV π hθ).restrict (thV_mem π hθ K hK)
    R := R
    hE1 := fun _ _ _ _ => rfl
    hE2 := fun _ _ _ _ => rfl
    hσ := fun w k u g => (rt_apply (kAt w k) g u.1.1).trans (along_unit w g _ k).symm
    hΘ := fun u g => ThInv.thV_apply π hθ u.1 g
    hR := hR }⟩

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.ExistsClass
section
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.GKCoh MeasureTheory GlobalTheory.CompanionTheory.TwY.ThInv
open PositivityTheory.Rg.BcB (thetaA)

private theorem exists_class (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : CuspSub E n)
    (hπ : GlobalTheory.DiscSpec.IsNormalised π) :
    ∃ B : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ ψ, starRingEnd ℂ (B φ ψ) = B ψ φ) ∧ (∀ φ, 0 ≤ (B φ φ).re) ∧
      (∀ φ, φ ≠ 0 → 0 < (B φ φ).re) ∧ (∀ (X : Lie E n) φ ψ, B (lieOp π X φ) ψ + B φ (lieOp π X ψ) = 0) ∧
      ∀ (g : GA E n) (φ ψ φ' ψ' : π.V), (∀ x, φ'.1.1 x = φ.1.1 (x * g)) → (∀ x, ψ'.1.1 x = ψ.1.1 (x * g)) →
        B φ' ψ' = B φ ψ := by
  obtain ⟨μ, hμ, hμ'⟩ := GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant E n
  have hl := GlobalTheory.CompanionTheory.CuspForms.memL2_and_bounded_of_normalised GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E n μ π hπ
  have hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E n) μ φ.1 := fun φ hφ => (hl φ hφ).1
  have inj : Function.Injective (toL2ₗ μ π.V hm) :=
    toL2ₗ_injective hm fun ψ hψ => ContAut.continuous_of_isOpen_stab E n ψ (π.cusp ψ hψ).1.level
  have sq : ∀ φ : π.V, (inner ℂ (toL2ₗ μ π.V hm φ) (toL2ₗ μ π.V hm φ)).re = ‖toL2ₗ μ π.V hm φ‖ ^ 2 := fun φ =>
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  refine ⟨((innerₛₗ ℂ).comp (toL2ₗ μ π.V hm)).compl₂ (toL2ₗ μ π.V hm), fun φ ψ =>
    inner_conj_symm (𝕜 := ℂ) (toL2ₗ μ π.V hm ψ) (toL2ₗ μ π.V hm φ), fun φ => ?_,
    fun φ hφ => ?_, fun X φ ψ => ?_, fun g φ ψ φ' ψ' h h' => ?_⟩
  · exact (sq φ).symm ▸ sq_nonneg _
  · exact (sq φ).symm ▸ pow_pos (norm_pos_iff.2 fun e => hφ (inj (e.trans (map_zero _).symm))) 2
  · have e := GlobalTheory.CompanionTheory.PeterssonSkew.lie_skew_adjoint E n μ π hm (fun φ hφ => (hl φ hφ).2) X ψ φ
    exact (add_comm _ _).trans (add_eq_zero_iff_eq_neg.2 e)
  · change inner ℂ (hm _ φ'.2).toL2 (hm _ ψ'.2).toL2 = inner ℂ (hm _ φ.2).toL2 (hm _ ψ.2).toL2
    rw [GlobalTheory.AutomorphicL2Unitary.MemL2Quotient.inner_toL2_eq_theta_pairing, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient.inner_toL2_eq_theta_pairing, funext h, funext h']
    exact GlobalTheory.CompanionTheory.PeterssonSkew.pet_mul_right μ (hm _ ψ.2) (hm _ φ.2) g

theorem UpperTheory.V.Z.GSp4Splitting.petEx :
    PetEx := by
  intro E _ _ _ n _ π hθ
  obtain ⟨B, hc, h0, hp, hL, hg⟩ := exists_class E n π hθ.1
  have hv := thV_apply π hθ
  set T := thV π hθ
  have hTL : ∀ (X : Lie E n) (φ : π.V), T (lieOp π X φ) = -lieOp π (adjH X) (T φ) := fun X φ => by
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    have e : φ.1.1 = fun y => (T φ).1.1 (thetaA E n y) := funext fun y => by
      rw [hv, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]
    have e2 := lieD_theta X (T φ).1.2 (thetaA E n x)
    rw [← e, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol] at e2
    exact (hv _ x).trans e2
  have ev : ∀ φ ψ, (B + (B.comp T).compl₂ T) φ ψ = B φ ψ + B (T φ) (T ψ) := fun _ _ => rfl
  refine ⟨B + (B.comp T).compl₂ T, fun φ ψ => ?_, fun φ hφ => ?_, fun X φ ψ => ?_, fun g φ ψ φ' ψ' h h' => ?_,
    fun φ ψ φ' ψ' h h' => ?_⟩
  · rw [ev, ev, map_add, hc, hc]
  · rw [ev, Complex.add_re]
    exact add_pos_of_pos_of_nonneg (hp φ hφ) (h0 _)
  · have e1 := hL X φ ψ
    have e2 := hL (adjH X) (T φ) (T ψ)
    rw [ev, ev, hTL, hTL, map_neg, map_neg, LinearMap.neg_apply]
    linear_combination e1 - e2
  · rw [ev, ev, hg g φ ψ φ' ψ' h h', hg (thetaA E n g) (T φ) (T ψ) (T φ') (T ψ')] <;> intro x
    · rw [hv, hv, h, map_mul, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]
    · rw [hv, hv, h', map_mul, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]
  · have k : ∀ a a' : π.V, (∀ x, a'.1.1 x = a.1.1 (thetaA E n x)) → T a = a' ∧ T a' = a := fun a a' e =>
      ⟨Subtype.ext (Subtype.ext (funext fun x => (hv a x).trans (e x).symm)),
        Subtype.ext (Subtype.ext (funext fun x => by rw [hv, e, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]))⟩
    rw [ev, ev, (k _ _ h).1, (k _ _ h).2, (k _ _ h').1, (k _ _ h').2, add_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.RlTheta
section
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

noncomputable section

open NumberField GlobalTheory.CuspRep PositivityTheory.Rg.BcB GlobalTheory.CompanionTheory.TwY GlobalTheory.CompanionTheory.TwY.ThInv
open scoped InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.GSp4Splitting

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem along_unitary (w : InfinitePlace E) (g : GA E n) (φ : GA E n → ℂ) (k : Un n) :
    Bridge.along w g φ k.1 = φ (g * kAt w k) := by
  classical
  have e : Bridge.atW (E := E) w k.1 = toL (locInf w (Unitary.toUnits k)).val := by
    funext i j v
    rw [Bridge.atW]
    exact (locInf_apply w (Unitary.toUnits k) i j v).symm
  rw [Bridge.along, e, chart_val]
  rfl

private theorem eop_theta (w : InfinitePlace E) (a b : Fin n) {φ φ' : Sm E n}
    (h : ∀ x, φ'.1 x = φ.1 (thetaA E n x)) (x : GA E n) :
    (Bridge.eopW w true a b φ).1 (thetaA E n x) = -(Bridge.eopW w false b a φ').1 x := by
  have e : φ'.1 = fun x => φ.1 (thetaA E n x) := funext h
  have e1 : ∀ (f : Sm E n) (y : GA E n), (Bridge.eopW w true a b f).1 y =
      (1 / 2 : ℂ) * (lieD (sg w a b 1) f.1 y - Complex.I * lieD (sg w a b Complex.I) f.1 y) := fun f y => by
    simp only [Bridge.eopW, if_true]
    exact Eop_apply _ a b f y
  have e2 : ∀ (f : Sm E n) (y : GA E n), (Bridge.eopW w false b a f).1 y =
      (1 / 2 : ℂ) * (lieD (sg w b a 1) f.1 y - Complex.I * lieD (sg w b a (-Complex.I)) f.1 y) := fun f y => by
    simp only [Bridge.eopW, Bool.false_eq_true, if_false]
    rw [Eop_apply, atEmb_conjugate, atEmb_conjugate]
    simp [sg]
  rw [e1, e2, e]
  simp only [lieD_theta _ φ.2, adjH_sg, map_one, map_neg, Complex.conj_I, neg_neg]
  ring

end

theorem rlTheta : RlTheta := by
  intro E _ _ _ n _ π _ K _ _ _ _ _ μf _ D
  have hext : ∀ x y : D.U, (∀ g, (D.i x).1.1 g = (D.i y).1.1 g) → x = y := fun x y h =>
    D.inj (Subtype.ext (Subtype.ext (funext h)))
  refine ⟨LinearMap.ext fun u => hext _ _ fun g => ?_, fun x y => ?_, fun w =>
    ⟨fun k => LinearMap.ext fun u => hext _ _ fun g => ?_, fun a b => LinearMap.ext fun u => hext _ _ fun g => ?_⟩⟩
  · change (D.i (D.Θ (D.Θ u))).1.1 g = (D.i u).1.1 g
    rw [D.hΘ, D.hΘ, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]
  · rw [D.inner_eq, D.inner_eq]
    exact D.pet.2.2.2.2 _ _ _ _ (D.hΘ x) (D.hΘ y)
  · change (D.i (D.Θ (D.σ w k u))).1.1 g = (D.i (D.σ w k (D.Θ u))).1.1 g
    rw [D.hΘ, D.hσ, D.hσ, along_unitary, along_unitary, D.hΘ, map_mul, thetaA_kAt]
  · change (D.i (D.Θ (D.E1 w a b u))).1.1 g = (D.i (D.E2 w a b (D.Θ u))).1.1 g
    rw [D.hΘ, D.hE1, D.hE2]
    exact eop_theta w a b (D.hΘ u) g

end UpperTheory.V.Z.GSp4Splitting
end
end

