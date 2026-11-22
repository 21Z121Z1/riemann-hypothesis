import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0004

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.PetInv
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem tw_rt (χ : HChar E) (g : GA E a) (φ : Sm E a) :
    mulChi a χ (rt E a g φ) = ((chiDet a χ g : ℂˣ) : ℂ)⁻¹ • rt E a g (mulChi a χ φ) := by
  rw [rt_mulChi, map_smul, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]

private theorem prod_fin (x : GL (Fin a) (Af E)) (φ : Sm E a) (l : List (Lie E a)) :
    (l.map (lie E a)).prod (act (.fin x) φ) = act (.fin x) ((l.map (lie E a)).prod φ) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, Module.End.mul_apply, ih]
    exact LinearMap.congr_fun (lie_rt_fin X x) _

private theorem prod_sq {r : ℝ} {φ : Sm E a} (h : IsSq r φ) (l : List (Lie E a)) :
    IsSq r ((l.map (lie E a)).prod φ) := by
  induction l with
  | nil => exact h
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact (sqLie E a r).1 X _ ih

private theorem sqInt_fin (ha : 1 ≤ a) {r : ℝ} {φ : Sm E a} (h : IsSq r φ) (x : GL (Fin a) (Af E)) :
    IsSqIntMod (act (.fin x) φ) := by
  obtain ⟨χ, hχ⟩ := twEx E a ha r
  obtain ⟨s, hs⟩ := hχ.1
  let μ : Measure (GA E a) := Measure.haar
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨h1, h2⟩ := sqMem E a ha μ r χ hχ φ (Submodule.subset_span h)
  have h3 := (sqUniq E a ha r χ hχ φ h.one (h.sq [])).1
  have hc : Continuous (mulChi a χ φ).1 := ContAut.continuous_of_isOpen_stab E a _ h1
  refine ⟨s, χ, hs, ?_⟩
  have e : (fun g => ((chiDet a χ g : ℂˣ) : ℂ) * (act (.fin x) φ).1 g) =
      ((chiDet a χ (finGL E a x) : ℂˣ) : ℂ)⁻¹ • fun g => (mulChi a χ φ).1 (g * finGL E a x) := by
    funext g
    exact (mul_comm _ _).trans (congrFun (congrArg Subtype.val (tw_rt χ (finGL E a x) φ)) g)
  rw [e]
  have h4 := h2.mul_right (finGL E a x)
  generalize ((chiDet a χ (finGL E a x) : ℂˣ) : ℂ)⁻¹ = c
  have hc' : Continuous fun g => (mulChi a χ φ).1 (g * finGL E a x) := hc.comp (continuous_id.mul continuous_const)
  refine (CuspidalL2GL.memL2_iff_isSqInt (μ := μ) (hc'.const_smul c) (fun γ g => ?_)
    (fun t g => ?_)).1 ⟨fun γ hγ g => congrArg (c • ·) (h4.1 γ hγ g), h4.2.const_smul c⟩
  · simp only [Pi.smul_apply, mul_assoc]
    rw [mulChi_apply, mulChi_apply, map_mul (chiDet a χ) (ratGL E a γ), chiDet_ratGL, one_mul, h.left]
  · simp only [Pi.smul_apply, mul_assoc, h3]

private theorem isSq_fin (ha : 1 ≤ a) {r : ℝ} (x : GL (Fin a) (Af E)) (φ : Sm E a) (h : IsSq r φ) :
    IsSq r (act (.fin x) φ) where
  left γ g := by
    change φ.1 (ratGL E a γ * g * finGL E a x) = φ.1 (g * finGL E a x)
    rw [mul_assoc, h.left]
  level := by
    have e : {k | act (.fin k) (act (.fin x) φ) = act (.fin x) φ} =
        (fun k => x⁻¹ * k * x) ⁻¹' {k | act (.fin k) φ = φ} := by
      ext k
      change finRep E a k (finRep E a x φ) = finRep E a x φ ↔ finRep E a (x⁻¹ * k * x) φ = φ
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      constructor
      · intro hk
        rw [hk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      · intro hk
        have := congrArg (finRep E a x) hk
        rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    rw [e]
    exact h.level.preimage (by fun_prop)
  one := by
    have e : lie E a (oneL E a) (act (.fin x) φ) = act (.fin x) (lie E a (oneL E a) φ) :=
      LinearMap.congr_fun (lie_rt_fin _ x) φ
    rw [e, h.one, map_smul]
  sq l := by
    rw [prod_fin]
    exact sqInt_fin ha (prod_sq h l) x

end

theorem UpperTheory.V.Cj.H.petInv :
    UpperTheory.V.Cj.H.PetInv := by
  intro E _ _ _ a ha r
  refine ⟨isSq_fin ha, ?_⟩
  obtain ⟨χ, hχ⟩ := twEx E a ha r
  let μ : Measure (GA E a) := Measure.haar
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  have hs := sqMem E a ha μ r χ hχ
  have hm : ∀ φ ∈ (sqSub E a r).map (mulChi a χ).toLinearMap, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (latticeGL E a) μ φ.1 := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (hs φ hφ).2
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (sqSub E a r).subtype (Submodule.ker_subtype _)
  obtain ⟨T, hT⟩ : ∃ T : Sm E a →ₗ[ℂ] GlobalTheory.AutomorphicL2Unitary.L2 (latticeGL E a) μ, ∀ φ (hφ : φ ∈ sqSub E a r),
      T φ = (hs φ hφ).2.toL2 := by
    refine ⟨CuspidalL2GL.toL2ₗ μ _ hm ∘ₗ (mulChi a χ).toLinearMap.submoduleMap (sqSub E a r) ∘ₗ p, fun φ hφ => ?_⟩
    have e : p φ = ⟨φ, hφ⟩ := LinearMap.congr_fun hp ⟨φ, hφ⟩
    simp only [LinearMap.comp_apply, e]
    rfl
  refine ⟨((innerₛₗ ℂ) ∘ₛₗ T).compl₂ T, ⟨fun x y => ?_, fun x _ => ?_, fun x hx h0 => ?_⟩, fun x => ?_⟩
  · exact (inner_conj_symm (T y) (T x)).symm
  · exact inner_self_nonneg (𝕜 := ℂ) (x := T x)
  · have h1 : T x = 0 := inner_self_eq_zero.1 (show inner ℂ (T x) (T x) = 0 from h0)
    rw [hT x hx] at h1
    by_contra hne
    refine CuspidalL2GL.toL2_ne_zero (hs x hx).2 (ContAut.continuous_of_isOpen_stab E a _ (hs x hx).1) (fun e => hne ?_) h1
    exact (mulChi a χ).map_eq_zero_iff.1 (Subtype.ext e)
  · set c : ℂ := ((chiDet a χ (finGL E a x) : ℂˣ) : ℂ)⁻¹ with hc
    have hst : sqSub E a r ≤ (sqSub E a r).comap (act (.fin x)) :=
      Submodule.span_le.2 fun ψ hψ => Submodule.subset_span (isSq_fin ha x ψ hψ)
    have key : ∀ φ ∈ sqSub E a r,
        T (act (.fin x) φ) = c • GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ (finGL E a x) (T φ) := fun φ hφ => by
      rw [hT _ (hst hφ), hT φ hφ, GlobalTheory.AutomorphicL2Unitary.right_translate_toL2]
      have h4 := (hs φ hφ).2.mul_right (finGL E a x)
      have h5 : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (latticeGL E a) μ (c • fun g => (mulChi a χ φ).1 (g * finGL E a x)) :=
        ⟨fun γ hγ g => congrArg (c • ·) (h4.1 γ hγ g), h4.2.const_smul c⟩
      refine Eq.trans ?_ (show h5.toL2 = c • h4.toL2 from MemLp.toLp_const_smul c h4.2)
      exact (GlobalTheory.AutomorphicL2Unitary.MemL2Quotient.toL2_eq_iff_ae_eq _ h5).2
        (.of_forall fun g => congrFun (congrArg Subtype.val (tw_rt χ (finGL E a x) φ)) g)
    refine ⟨starRingEnd ℂ c * c, fun φ hφ ψ hψ => ?_⟩
    change inner ℂ (T (act (.fin x) φ)) (T (act (.fin x) ψ)) = _ * inner ℂ (T φ) (T ψ)
    have hi : inner ℂ (GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ (finGL E a x) (T φ))
        (GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ (finGL E a x) (T ψ)) = inner ℂ (T φ) (T ψ) :=
      (LinearIsometry.mk (GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ (finGL E a x)).toLinearMap
        (GlobalTheory.AutomorphicL2Unitary.norm_R _)).inner_map_map _ _
    rw [key φ hφ, key ψ hψ, inner_smul_left, inner_smul_right, hi, mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.PoinOp
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} (G : Dr.Geo Γ V S d)

private theorem tr_tr (q : ℕ) (γ δ : Γ) (h : γ * δ = 1) (m : V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) :
    G.tr q γ (G.tr q δ m) = m := by
  have hδ : δ = γ⁻¹ := eq_inv_of_mul_eq_one_right h
  subst hδ
  ext v
  rw [Geo.tr_apply, Geo.tr_apply, Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one,
    Matrix.one_mulVec]
  have hv : (fun i => (G.ρ γ⁻¹⁻¹) ((G.ρ γ⁻¹) (v i))) = v := by
    funext i
    exact Geo.ρ_inv_apply G γ⁻¹ (v i)
  rw [hv]

private theorem tr_coneOp (q : ℕ) (γ : Γ) (w : V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) (p x : V) :
    G.tr q γ (coneOp p w (G.ρ γ⁻¹ x)) = coneOp (G.ρ γ p) (fun y => G.tr (q + 1) γ (w (G.ρ γ⁻¹ y))) x := by
  let L : (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) ≃L[ℝ] (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) :=
    ContinuousLinearEquiv.equivOfInverse (G.tr q γ) (G.tr q γ⁻¹)
      (fun m => tr_tr G q γ⁻¹ γ (inv_mul_cancel γ) m)
      (fun m => tr_tr G q γ γ⁻¹ (mul_inv_cancel γ) m)
  have hL : ∀ m, L m = G.tr q γ m := fun m => rfl
  have key : ∀ f : ℝ → (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)),
      L (∫ t in (0:ℝ)..1, f t) = ∫ t in (0:ℝ)..1, L (f t) := by
    intro f
    simp only [intervalIntegral, map_sub, L.integral_comp_comm]
  have hpt : ∀ t : ℝ, G.ρ γ⁻¹ (G.ρ γ p + t • (x - G.ρ γ p)) = p + t • (G.ρ γ⁻¹ x - p) := by
    intro t
    simp [map_add, map_smul, map_sub, Geo.ρ_inv_apply]
  rw [← hL]
  unfold coneOp
  rw [key]
  congr 1
  funext t
  rw [map_smul]
  beta_reduce
  rw [hpt]
  congr 1
  ext v
  rw [hL, Geo.tr_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply, Geo.tr_apply]
  congr 2
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [Geo.ρ_inv_apply]
  · intro j
    simp

end

theorem UpperTheory.V.Cj.H.poinOp :
    UpperTheory.V.Cj.H.PoinOp := by
  intro Γ V S _ _ _ _ d G hconv q
  classical
  have hD := coneD V (Fin d → ℂ) G.Y G.isOpen hconv
  let f : V → G.Om (q + 1) → S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ) :=
    fun p w s x => if x ∈ G.Y then coneOp p ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) x else 0
  have hwm : ∀ (w : G.Om (q + 1)) (s : S),
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
        ∀ x ∉ G.Y, (w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s x = 0 := fun w => w.2
  have hf : ∀ p ∈ G.Y, ∀ w, f p w ∈ G.Om q := by
    intro p hp w
    refine fun s => ⟨?_, ?_⟩
    · exact ((hD p hp q _ (hwm w s).1).1).congr (fun x hx => if_pos hx)
    · intro x hx
      exact if_neg hx
  let K : V → G.Om (q + 1) → G.Om q := fun p w => if hp : p ∈ G.Y then ⟨f p w, hf p hp w⟩ else 0
  have hK : ∀ p (hp : p ∈ G.Y) w, ((K p w : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) = f p w := by
    intro p hp w
    simp [K, hp]
  refine ⟨K, ?_, ?_, ?_⟩
  · intro p hp w hw0
    apply Subtype.ext
    funext s x
    by_cases hx : x ∈ G.Y
    · rw [Geo.dOm_apply G (K p w) s hx, hK p hp w]
      have hclosed : ∀ y ∈ G.Y, extDeriv ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) y = 0 := by
        intro y hy
        have h0 := congrArg
          (fun u : G.Om (q + 1 + 1) => (u : S → V → V [⋀^Fin (q + 1 + 1)]→L[ℝ] (Fin d → ℂ)) s y) hw0
        rw [Geo.dOm_apply G w s hy] at h0
        simpa using h0
      have hloc : extDeriv (f p w s) x =
          extDeriv (coneOp p ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s)) x := by
        rw [← extDerivWithin_univ, ← extDerivWithin_univ]
        apply Filter.EventuallyEq.extDerivWithin_eq_of_mem _ (Set.mem_univ x)
        rw [nhdsWithin_univ]
        exact Filter.eventually_of_mem (G.isOpen.mem_nhds hx) (fun y hy => if_pos hy)
      rw [hloc]
      exact (hD p hp q _ (hwm w s).1).2 hclosed x hx
    · have h1 := ((G.dOm q (K p w)).2 s).2 x hx
      have h2 := (hwm w s).2 x hx
      rw [h1, h2]
  · intro γ p hp w
    have hp' : G.ρ γ p ∈ G.Y := G.maps γ p hp
    apply Subtype.ext
    funext s x
    show G.tr q γ (((K p w : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x)) =
      ((K (G.ρ γ p) (G.act (q + 1) γ w) : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x
    rw [hK p hp, hK _ hp']
    by_cases hx : x ∈ G.Y
    · have hx' : G.ρ γ⁻¹ x ∈ G.Y := G.maps γ⁻¹ x hx
      simp only [f, if_pos hx, if_pos hx']
      exact tr_coneOp G q γ _ p x
    · have hx' : G.ρ γ⁻¹ x ∉ G.Y := by
        intro h
        apply hx
        have h2 := G.maps γ _ h
        have h3 := Geo.ρ_inv_apply G γ⁻¹ x
        rw [inv_inv] at h3
        rwa [h3] at h2
      simp only [f, if_neg hx, if_neg hx', map_zero]
  · intro p hp w hw s C hC hCc
    have h := coneLim V (Fin d → ℂ) G.Y hconv p hp q
      (fun k => ((w k : G.Om (q + 1)) : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s)
      (fun C' hC' hC'c => hw s C' hC' hC'c) C hC hCc
    refine h.congr ?_
    filter_upwards with k
    intro x hx
    rw [hK p hp]
    simp [f, hC hx]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.WigSub
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

namespace UpperTheory.V.Cj.H.WignerSubquotient

private theorem mapQ {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) u := by
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
    Function.comp_def, map_add, apply_ite f, AlgHom.commutes, map_zero]

private theorem relQ {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (S : Subalgebra ℂ (A × B)) {n : ℕ}
    (X : Fin n → Fin n → A) (Y : Fin n → Fin n → B) (h : ∀ p q, (X p q, Y p q) ∈ S) (v : ℂ) :
    (Formalism.REAL.qdet X v, Formalism.REAL.qdet Y v) ∈ S := by
  let Z : Fin n → Fin n → S := fun p q => ⟨(X p q, Y p q), h p q⟩
  have e1 : ((Formalism.REAL.qdet Z v : S) : A × B).1 = Formalism.REAL.qdet X v := mapQ ((AlgHom.fst ℂ _ _).comp S.val) Z v
  have e2 : ((Formalism.REAL.qdet Z v : S) : A × B).2 = Formalism.REAL.qdet Y v := mapQ ((AlgHom.snd ℂ _ _).comp S.val) Z v
  rw [← e1, ← e2]
  exact (Formalism.REAL.qdet Z v).2

section

variable {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']

private theorem intQ {k : ℕ} (R : M →ₗ[ℂ] M') (X : Fin k → Fin k → Module.End ℂ M) (Y : Fin k → Fin k → Module.End ℂ M')
    (h : ∀ p q m, R (X p q m) = Y p q (R m)) (v : ℂ) (m : M) :
    R (Formalism.REAL.qdet X v m) = Formalism.REAL.qdet Y v (R m) := by
  let S : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ M') :=
    { carrier := {z | ∀ m, R (z.1 m) = z.2 (R m)}
      mul_mem' := fun {x y} hx hy m => (hx _).trans (congrArg x.2 (hy m))
      add_mem' := fun {x y} hx hy m => (map_add R _ _).trans (congrArg₂ (· + ·) (hx m) (hy m))
      algebraMap_mem' := fun c m => map_smul R c m }
  exact relQ S X Y h v m

private theorem intQop {k : ℕ} (R : M →ₗ[ℂ] M') (X : Fin k → Fin k → Module.End ℂ M) (Y : Fin k → Fin k → Module.End ℂ M')
    (h : ∀ p q m, R (X p q m) = Y p q (R m)) (v : ℂ) (m : M) :
    R ((Formalism.REAL.qdet (fun i j => -MulOpposite.op (X i j)) v).unop m) =
      (Formalism.REAL.qdet (fun i j => -MulOpposite.op (Y i j)) v).unop (R m) := by
  let S : Subalgebra ℂ ((Module.End ℂ M)ᵐᵒᵖ × (Module.End ℂ M')ᵐᵒᵖ) :=
    { carrier := {z | ∀ m, R (z.1.unop m) = z.2.unop (R m)}
      mul_mem' := fun {x y} hx hy m => (hy _).trans (congrArg y.2.unop (hx m))
      add_mem' := fun {x y} hx hy m => (map_add R _ _).trans (congrArg₂ (· + ·) (hx m) (hy m))
      algebraMap_mem' := fun c m => map_smul R c m }
  exact relQ S (fun i j => -MulOpposite.op (X i j)) (fun i j => -MulOpposite.op (Y i j))
    (fun p q m => (map_neg R _).trans (congrArg Neg.neg (h p q m))) v m

end

variable {E : Type} [Field E] {a : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]

private noncomputable def res (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (N : Submodule ℂ M) (h : ∀ X, ∀ m ∈ N, L X m ∈ N) :
    Lie E a →ₗ[ℝ] Module.End ℂ N where
  toFun X := (L X).restrict (h X)
  map_add' X Y := LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (map_add L X Y) m.1)
  map_smul' c X := LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (map_smul L c X) m.1)

private theorem res_hom {L : Lie E a →ₗ[ℝ] Module.End ℂ M} (hL : IsLieHom L) (N : Submodule ℂ M)
    (h : ∀ X, ∀ m ∈ N, L X m ∈ N) : IsLieHom (res L N h) :=
  fun X Y => LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (hL X Y) m.1)

private theorem res_dCo {L : Lie E a →ₗ[ℝ] Module.End ℂ M} {N : Submodule ℂ M} {L' : Lie E a →ₗ[ℝ] Module.End ℂ N}
    (h : ∀ X m, (L' X m : M) = L X m) {q : ℕ} (ω' : Herm E a [⋀^Fin q]→ₗ[ℝ] N) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M)
    (hω : ∀ Y, (ω' Y : M) = ω Y) (Y : Fin (q + 1) → Herm E a) : (dCo L' ω' Y : M) = dCo L ω Y := by
  rw [dCo_apply, dCo_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hω, ← h]
  exact map_zsmul N.subtype _ _

end UpperTheory.V.Cj.H.WignerSubquotient

open UpperTheory.V.Cj.H.WignerSubquotient in
theorem UpperTheory.V.Cj.H.wigSub :
    UpperTheory.V.Cj.H.WigSub := by
  intro E _ _ _ a M _ _ _ _ LA LB hA hB hAB N sA sB τ x z hz
  subst hz
  refine ⟨?_, fun q ω h1 h2 hN => ?_⟩
  · obtain ⟨α, p1, p2⟩ := wigAlpha E a M LA LB hA hB hAB τ x
    exact (wigHom E a M (LA + LB) α _ p1 p2).1
  · obtain ⟨α, p1, p2⟩ := wigAlpha E a N (res LA N sA) (res LB N sB) (res_hom hA N sA) (res_hom hB N sB)
      (fun X Y => LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (hAB X Y) m.1)) τ x
    let ω' : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] N :=
      { toFun := fun Y => ⟨ω Y, hN Y⟩
        map_update_add' := fun Y i u v => Subtype.ext (ω.map_update_add Y i u v)
        map_update_smul' := fun Y i c u => Subtype.ext (ω.map_update_smul Y i c u)
        map_eq_zero_of_eq' := fun Y i j e hij => Subtype.ext (ω.map_eq_zero_of_eq Y e hij) }
    have hL : ∀ X (m : N), ((res LA N sA + res LB N sB) X m : M) = (LA + LB) X m := fun _ _ => rfl
    obtain ⟨η, hη⟩ := (wigHom E a N (res LA N sA + res LB N sB) α _ p1 p2).2 q ω'
      (fun Z hZ Y => Subtype.ext ((h1 Z hZ Y).trans
        (Submodule.coe_sum N (fun i => ω' (Function.update Y i (brH Z hZ (Y i)))) Finset.univ).symm))
      (AlternatingMap.ext fun Y => Subtype.ext ((res_dCo hL ω' ω (fun _ => rfl) Y).trans (by rw [h2]; rfl)))
    refine ⟨(N.subtype.restrictScalars ℝ).compAlternatingMap η, fun Y => (η Y).2, fun Y => ?_⟩
    rw [← res_dCo hL η _ (fun _ => rfl) Y, hη, LinearMap.sub_apply, LinearMap.sub_apply, Submodule.coe_sub]
    exact congrArg₂ (· - ·) (intQ N.subtype _ (eL LA τ) (fun _ _ _ => rfl) x (ω' Y))
      (intQop N.subtype _ (eL LB τ) (fun _ _ _ => rfl) x (ω' Y))
end

