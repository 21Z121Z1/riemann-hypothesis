import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.LieOneEqZero
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo
open scoped TensorProduct

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem chart_prod (f h : GA E a → ℂ) (g : GA E a) :
    chart (fun x => f x * h x) g = fun y => chart f g y * chart h g y := by
  funext y
  unfold chart
  split_ifs <;> simp

private def mulOp (u : Sm E a) : Module.End ℂ (Sm E a) where
  toFun φ := ⟨fun x => u.1 x * φ.1 x, fun g => by
    rw [chart_prod]
    exact (u.2 g).mul (φ.2 g)⟩
  map_add' φ ψ := Subtype.ext (funext fun x => mul_add _ _ _)
  map_smul' c φ := Subtype.ext (funext fun x => mul_left_comm _ c _)

private theorem mulOp_apply (u φ : Sm E a) (g : GA E a) : (mulOp u φ).1 g = u.1 g * φ.1 g := rfl

private theorem lie_mulOp (X : Lie E a) (u φ : Sm E a) :
    lie E a X (mulOp u φ) = mulOp u (lie E a X φ) + mulOp (lie E a X u) φ := by
  refine Subtype.ext (funext fun g => ?_)
  have hv : ∀ f : GA E a → ℂ, chart f g (oneL E a) = f g := fun f => by
    simpa using chart_val f g 1
  change fderiv ℝ (chart (fun x => u.1 x * φ.1 x) g) (oneL E a) X =
    u.1 g * fderiv ℝ (chart φ.1 g) (oneL E a) X + fderiv ℝ (chart u.1 g) (oneL E a) X * φ.1 g
  rw [chart_prod, fderiv_fun_mul (differentiableAt_chart u.2 g) (differentiableAt_chart φ.2 g), hv, hv]
  simp [mul_comm]

private theorem ev_mulOp {d : ℕ} (u : Sm E a) (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) :
    ev ((mulOp u).rTensor _ m) g = u.1 g • ev m g := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v => rw [LinearMap.rTensor_tmul, ev_tmul, ev_tmul, mulOp_apply, mul_smul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, smul_add]

private theorem smLie_mulOp (Ξ : AlgRep E a) (X : Lie E a) (u : Sm E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    smLie Ξ X ((mulOp u).rTensor _ m) =
      (mulOp u).rTensor _ (smLie Ξ X m) + (mulOp (lie E a X u)).rTensor _ m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    change lie E a X (mulOp u φ) ⊗ₜ[ℂ] v + mulOp u φ ⊗ₜ[ℂ] (Ξ.dmat X *ᵥ v) =
      (mulOp u).rTensor _ (lie E a X φ ⊗ₜ[ℂ] v + φ ⊗ₜ[ℂ] (Ξ.dmat X *ᵥ v)) + mulOp (lie E a X u) φ ⊗ₜ[ℂ] v
    rw [lie_mulOp, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.add_tmul]
    abel
  | add x y hx hy => simp only [map_add, hx, hy]; abel

private theorem smK_mulOp (Ξ : AlgRep E a) (k : Kinf E a) (u : Sm E a) (hu : act (.cpt k) u = u)
    (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    smK Ξ k ((mulOp u).rTensor _ m) = (mulOp u).rTensor _ (smK Ξ k m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    have h : act (.cpt k) (mulOp u φ) = mulOp (act (.cpt k) u) (act (.cpt k) φ) := rfl
    simp only [smK, LinearMap.rTensor_tmul, TensorProduct.map_tmul, h, hu]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem lie_one_eq_zero (u : Sm E a) (hu : ∀ t g, u.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = u.1 g) :
    lie E a (oneL E a) u = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  let c : ℝ → GL (Fin a) (Cinf E) := fun t =>
    Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ))
  have hc : ∀ t, infGL E a (c t) = GlobalTheory.UnitaryBC.splitCentre E a t := fun _ => rfl
  have hval : ∀ t : ℝ, toL (c t).val = Complex.exp t • oneL E a := fun t => by
    ext i j w
    by_cases h : i = j <;> simp [c, expU, toL, oneL, h, Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  have h0 : c 0 = 1 := Units.ext (by
    have h := hval 0
    rw [Complex.ofReal_zero, Complex.exp_zero, one_smul] at h
    exact h)
  have hd : HasDerivAt (fun t => toL (c t).val) (oneL E a) 0 := by
    simp only [hval]
    simpa using ((Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal).smul_const (oneL E a)
  have h1 := GlobalTheory.CuspRep.hasDerivAt_curve u g c _ h0 hd
  simp only [hc, ← CuspidalL2GL.splitCentre_comm, hu] at h1
  exact h1.unique (hasDerivAt_const _ _)

private theorem levelFn_mulOp {U : Subgroup (GL (Fin a) (Af E))} {Ξ : AlgRep E a} {u φ : Sm E a} (hu : IsCut U u)
    (hφ : IsLevelFn U Ξ φ) : IsLevelFn U Ξ (mulOp u φ) := by
  refine ⟨fun γ g => ?_, fun k hk => ?_, fun m hm => ?_⟩
  · rw [mulOp_apply, mulOp_apply, hu.left, hφ.1]
  · have h : act (.fin k) (mulOp u φ) = mulOp (act (.fin k) u) (act (.fin k) φ) := rfl
    rw [h, hu.level k hk, hφ.2.1 k hk]
  · have h : mulOp (0 : Sm E a) φ = 0 := Subtype.ext (funext fun x => zero_mul _)
    rw [lie_mulOp, lie_one_eq_zero u hu.centre, h, add_zero, hφ.2.2 m hm, map_smul]

private theorem ev_dCo (Ξ : AlgRep E a) {q : ℕ} (ω : Co Ξ q) (X : Fin (q + 1) → Herm E a) (g : GA E a) :
    ev (dCo (smLie Ξ) ω X) g =
      ∑ i : Fin (q + 1), (-1 : ℂ) ^ (i : ℕ) • ev (smLie Ξ (toL (X i).1) (ω (i.removeNth X))) g := by
  rw [dCo, AlternatingMap.alternatizeUncurryFin_apply, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Pi.smul_apply, ← Int.cast_smul_eq_zsmul ℂ]
  push_cast
  rfl

end

theorem UpperTheory.V.Lit.Geo.mulEx :
    MulEx := by
  intro E _ _ _ a U Ξ q u α hu hα
  refine ⟨(((mulOp u).rTensor (Fin Ξ.d → ℂ)).restrictScalars ℝ).compAlternatingMap α,
    ⟨fun k => ?_, fun X i hi => ?_, fun X => ?_⟩, fun X g => ev_mulOp u (α X) g, fun X g => ?_⟩
  · intro X
    change (mulOp u).rTensor _ (α _) = smK Ξ k ((mulOp u).rTensor _ (α X))
    rw [smK_mulOp Ξ k u (hu.cpt k), hα.equiv k X]
  · change (mulOp u).rTensor _ (α X) = 0
    rw [hα.basic X i hi, map_zero]
  · change (mulOp u).rTensor _ (α X) ∈ _
    refine Submodule.span_induction (p := fun m _ => (mulOp u).rTensor _ m ∈ _) ?_ ?_ ?_ ?_ (hα.val X)
    · rintro _ ⟨φ, v, hφ, rfl⟩
      exact Submodule.subset_span ⟨_, v, levelFn_mulOp hu hφ, LinearMap.rTensor_tmul _ _ _ _⟩
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [map_smul]; exact Submodule.smul_mem _ c hx
  · rw [ev_dCo, ev_dCo, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    change _ • ev (smLie Ξ _ ((mulOp u).rTensor _ (α _))) g = _
    rw [smLie_mulOp, map_add, Pi.add_apply, ev_mulOp, ev_mulOp, smul_add, smul_comm, mul_smul]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.NormEucSq
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.Lit.Geo

def Scale {ι : Type} (q : ι → ℝ) (N : ℕ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ ∀ s t : ℝ, 0 < s → s ≤ t → (Summable fun i => Real.exp (-Real.pi * (s * q i))) ∧
    ∑' i, Real.exp (-Real.pi * (s * q i)) ≤ (t / s) ^ N * ∑' i, Real.exp (-Real.pi * (t * q i))

section Inf

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def qf (x : Fin a → Cinf E) : ℝ := ∑ i, ∑ w : InfinitePlace E, ‖x i w‖ ^ 2

def euc : (Fin a → Cinf E) ≃ₗ[ℝ] EuclideanSpace ℂ (Fin a × InfinitePlace E) where
  toFun x := WithLp.toLp 2 fun p => x p.1 p.2
  invFun y := fun i w => y.ofLp (i, w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem norm_euc_sq (x : Fin a → Cinf E) : ‖euc x‖ ^ 2 = qf x := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

theorem qf_nonneg (x : Fin a → Cinf E) : 0 ≤ qf x := norm_euc_sq x ▸ sq_nonneg _

def gauss (x : Fin a → Cinf E) : ℝ := Real.exp (-Real.pi * qf x)

def quad (p : Matrix (Fin a) (Fin a) (Cinf E)) (x : Fin a → Cinf E) : ℝ :=
  ∑ w : InfinitePlace E, (((x ᵥ* p) ⬝ᵥ star x) w).re

variable (E a) in

def poly : Subalgebra ℂ ((Fin a → Cinf E) → ℂ) :=
  Algebra.adjoin ℂ (Set.range fun l : (Fin a → Cinf E) →ₗ[ℝ] ℂ => (l : (Fin a → Cinf E) → ℂ))

def pg (P : (Fin a → Cinf E) → ℂ) (x : Fin a → Cinf E) : ℂ := P x * (gauss x : ℝ)

def sc (y : Matrix (Fin a) (Fin a) (Cinf E)) : ℝ :=
  Real.exp (-((∑ w : InfinitePlace E, Real.log ‖y.det w‖) / ((a : ℝ) * Fintype.card (InfinitePlace E))))

def msum {ι : Type} (x : ι → Fin a → Cinf E) (P : (Fin a → Cinf E) → ℂ) (y : Lie E a) : ℂ :=
  ∑' i, pg P (x i ᵥ* Matrix.of y)

structure IsLat (L : AddSubgroup (Fin a → Af E)) : Prop where
  isOpen : IsOpen (L : Set (Fin a → Af E))
  isCompact : IsCompact (L : Set (Fin a → Af E))

def vFin (v : Fin a → E) : Fin a → Af E := fun i => algebraMap E (Af E) (v i)

def ptF (g : GA E a) : (Fin a → E) →+ (Fin a → Af E) where
  toFun v := vFin v ᵥ* (GeneralLinearGroup.map (pFin E) g).val
  map_zero' := by
    have h : vFin (0 : Fin a → E) = 0 := funext fun _ => map_zero _
    rw [h, Matrix.zero_vecMul]
  map_add' v v' := by
    have h : vFin (v + v') = vFin v + vFin v' := funext fun _ => map_add _ _ _
    rw [h, Matrix.add_vecMul]

def lat (L : AddSubgroup (Fin a → Af E)) (g : GA E a) : AddSubgroup (Fin a → E) := L.comap (ptF g)

variable [IsTotallyComplex E]

def vInf (v : Fin a → E) : Fin a → Cinf E := fun i => pInf E (algebraMap E (Ad E) (v i))

def pt (g : GA E a) : (Fin a → E) →+ (Fin a → Cinf E) where
  toFun v := vInf v ᵥ* (GeneralLinearGroup.map (pInf E) g).val
  map_zero' := by
    have h : vInf (0 : Fin a → E) = 0 := funext fun _ => by simp [vInf]
    rw [h, Matrix.zero_vecMul]
  map_add' v v' := by
    have h : vInf (v + v') = vInf v + vInf v' := funext fun _ => by simp [vInf]
    rw [h, Matrix.add_vecMul]

def rt (g : GA E a) : GA E a := (retractOne g : KernelIndexFullLattice.G1 E a).1

def gsum {M : Type} [AddCommMonoid M] [TopologicalSpace M] (L : AddSubgroup (Fin a → Af E)) (F : (Fin a → Cinf E) → M)
    (g : GA E a) : M := ∑' v : lat L g, F (pt (rt g) v.1)

def Th (L : AddSubgroup (Fin a → Af E)) (g : GA E a) : ℝ := gsum L gauss g

def fn (L : AddSubgroup (Fin a → Af E)) (g : GA E a) : ℝ := Real.log (Th L g)

def mean (L : AddSubgroup (Fin a → Af E)) (P : (Fin a → Cinf E) → ℂ) (g : GA E a) : ℂ := gsum L (pg P) g / (Th L g : ℝ)

def mom (L : AddSubgroup (Fin a → Af E)) (g : GA E a) : Herm E a :=
  ⟨Matrix.of fun i j w => mean L (fun x => star (x i w) * x j w) g, by
    change star _ = _
    ext i j w
    simp only [Matrix.star_apply, Matrix.of_apply, Pi.star_apply, mean, gsum, pg, star_div₀, tsum_star, star_mul',
      star_star, Complex.star_def, Complex.conj_ofReal, Complex.conj_tsum, map_mul, Complex.conj_conj, mul_comm]⟩

def dev (L : AddSubgroup (Fin a → Af E)) (g : GA E a) : Herm E a :=
  mom L g - ell E a (toL (mom L g).1) • (⟨1, IsSelfAdjoint.one _⟩ : Herm E a)

def meanAlg (L : AddSubgroup (Fin a → Af E)) : Subalgebra ℂ (GA E a → ℂ) :=
  Algebra.adjoin ℂ {f | ∃ P ∈ poly E a, f = mean L P}

end Inf

end UpperTheory.V.Lit.Geo
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
section
noncomputable section

open NumberField Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL

namespace UpperTheory.V.Lit.Geo.Pf

section Defs

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

structure CInv (F : GA E a → ℂ) : Prop where
  cont : Continuous F
  left : ∀ γ g, F (ratGL E a γ * g) = F g
  centre : ∀ t g, F (splitCentre E a t * g) = F g

structure SInv (φ : Sm E a) : Prop where
  left : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g
  centre : ∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g
  level : IsOpen {k | act (.fin k) φ = φ}

def Cs {M : Type} [Zero M] (F : GA E a → M) : Prop := ∃ R : ℝ, ∀ g, R < qht g → F g = 0

def QInt (μ : Measure (GA E a)) (F : GA E a → ℂ) : Prop :=
  Integrable (fun x : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a) => F x.out) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)

def qint (μ : Measure (GA E a)) (F : GA E a → ℂ) : ℂ :=
  ∫ x : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a), F x.out ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)

def TwInv (χ : HChar E) {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) : Prop := ∀ j, SInv (mulChi a χ (cmp j m))

def pt (χ : HChar E) {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) : ℂ :=
  (‖((chiDet a χ g : ℂˣ) : ℂ)‖ ^ 2 : ℝ) * (star (ev x g) ⬝ᵥ G *ᵥ ev y g)

theorem cmp_ev {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) (g : GA E a) : (cmp j m).1 g = ev m g j := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v => simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

theorem ptIp_eq {Ξ : AlgRep E a} {q : ℕ} (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) {n : ℕ} (e : Fin n → Herm E a)
    (α β : Co Ξ q) (g : GA E a) :
    ptIp χ G e α β g = ∑ I : Fin q → Fin n, pt χ G (α fun i => e (I i)) (β fun i => e (I i)) g := by
  simp only [ptIp, pt, Finset.mul_sum]

theorem CInv.sum {ι : Type} (s : Finset ι) {F : ι → GA E a → ℂ} (h : ∀ i, CInv (F i)) : CInv fun g => ∑ i ∈ s, F i g :=
  ⟨continuous_finset_sum _ fun i _ => (h i).cont, fun γ g => Finset.sum_congr rfl fun i _ => (h i).left γ g,
    fun t g => Finset.sum_congr rfl fun i _ => (h i).centre t g⟩

theorem cs_pt_left (χ : HChar E) {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) {x : Sm E a ⊗[ℂ] (Fin d → ℂ)} (y : Sm E a ⊗[ℂ] (Fin d → ℂ))
    (h : Cs (ev x)) : Cs (pt χ G x y) :=
  h.imp fun _ hR g hg => by simp [pt, hR g hg]

theorem cs_pt_right (χ : HChar E) {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) (x : Sm E a ⊗[ℂ] (Fin d → ℂ)) {y : Sm E a ⊗[ℂ] (Fin d → ℂ)}
    (h : Cs (ev y)) : Cs (pt χ G x y) :=
  h.imp fun _ hR g hg => by simp [pt, hR g hg]

end Defs

def InvLie : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), SInv φ →
    CInv φ.1 ∧ ∀ X : Lie E a, SInv (lie E a X φ)

def BddInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (F : GA E a → ℂ), CInv F → (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → QInt μ F ∧ GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (latticeGL E a) μ F

def CsBdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ), CInv F →
    (Cs F ∨ ∃ C : ℝ, ∀ g : KernelIndexFullLattice.G1 E a, ‖F g.1‖ ≤ C) → ∃ C : ℝ, ∀ g, ‖F g‖ ≤ C

def CsLie : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (X : Lie E a), Cs φ.1 → Cs (lie E a X φ).1

def ProdEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ ψ : Sm E a), ∃ θ : Sm E a,
    (∀ g, θ.1 g = starRingEnd ℂ (φ.1 g) * ψ.1 g) ∧
    ∀ (X : Lie E a) g, (lie E a X θ).1 g =
      starRingEnd ℂ ((lie E a X φ).1 g) * ψ.1 g + starRingEnd ℂ (φ.1 g) * (lie E a X ψ).1 g

def StokesFn : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (θ : Sm E a) (X : Lie E a), SInv θ → Cs θ.1 → qint μ (lie E a X θ).1 = 0

def LevInv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E), HasOne Ξ r → IsTw (a := a) r χ →
    ∀ (q : ℕ) (α : Co Ξ q), IsLev U Ξ α → ∀ X, TwInv χ (α X)

def PtInv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (χ : HChar E) (d : ℕ) (G : Matrix (Fin d) (Fin d) ℂ)
    (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)),
    (∀ g, pt χ G x y g = ∑ i, ∑ j, G i j *
      (starRingEnd ℂ ((mulChi a χ (cmp i x)).1 g) * (mulChi a χ (cmp j y)).1 g)) ∧
    ((TwInv χ x → TwInv χ y → CInv (pt χ G x y)) ∧
      ∀ θ : Sm E a, (∀ g, θ.1 g = pt χ G x y g) → TwInv χ x → TwInv χ y → SInv θ)

def TwLie : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E),
    IsTw (a := a) r χ → ∀ (X : Lie E a) (x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)), TwInv χ x →
      TwInv χ (smLie Ξ X x) ∧ TwInv χ (smAdj Ξ r X x)

def CsTens : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (r : ℝ) (X : Lie E a)
    (x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)), Cs (ev x) → Cs (ev (smLie Ξ X x)) ∧ Cs (ev (smAdj Ξ r X x))

def PtDiv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E)
    (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), IsTw (a := a) r χ → IsAdm Ξ G → ∀ x y : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ),
    ∃ θ : Sm E a, (∀ g, θ.1 g = pt χ G x y g) ∧ ∀ (X : Herm E a) g,
      (lie E a (toL X.1) θ).1 g = pt χ G x (smLie Ξ (toL X.1) y) g - pt χ G (smAdj Ξ r (toL X.1) x) y g

def AdjInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), IsTw (a := a) r χ → IsAdm Ξ G →
    ∀ (X : Herm E a) (x y : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)), TwInv χ x → TwInv χ y → Cs (ev x) ∨ Cs (ev y) →
      QInt μ (pt χ G x (smLie Ξ (toL X.1) y)) ∧ QInt μ (pt χ G (smAdj Ξ r (toL X.1) x) y) ∧
        qint μ (pt χ G x (smLie Ξ (toL X.1) y)) = qint μ (pt χ G (smAdj Ξ r (toL X.1) x) y)

def PtD : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (χ : HChar E)
    (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (n : ℕ) (e : Fin n → Herm E a) (q : ℕ)
    (L : Lie E a →ₗ[ℝ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) (β : Co Ξ (q + 1)) (η : Co Ξ q) (g : GA E a),
    ptIp χ G e β (dCo L η) g = ((q : ℂ) + 1) * ∑ J : Fin q → Fin n, ∑ j,
        pt χ G (β (Matrix.vecCons (e j) fun i => e (J i))) (L (toL (e j).1) (η fun i => e (J i))) g ∧
      ptIp χ G e (del L e β) η g = ∑ J : Fin q → Fin n, ∑ j,
        pt χ G (L (toL (e j).1) (β (Matrix.vecCons (e j) fun i => e (J i)))) (η fun i => e (J i)) g

def ChiOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (χ : HChar E) (s : ℝ), χ.IsAbsPow s →
    ∀ g : KernelIndexFullLattice.G1 E a, ‖((chiDet a χ g.1 : ℂˣ) : ℂ)‖ = 1

def RapidBdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (χ : HChar E) (s : ℝ), χ.IsAbsPow s →
    ∀ (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (n : ℕ) (e : Fin n → Herm E a) (q : ℕ) (α β : Co Ξ q), Rapid α → Moderate β →
      ∃ C : ℝ, ∀ g : KernelIndexFullLattice.G1 E a, ‖ptIp χ G e α β g.1‖ ≤ C

def ZeroInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (F : GA E a → ℂ), CInv F → (∀ g, ∃ t : ℝ, 0 ≤ t ∧ F g = t) → QInt μ F → qint μ F = 0 → ∀ g, F g = 0

def PtPos : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (χ : HChar E)
    (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), IsAdm Ξ G → ∀ (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (q : ℕ) (α : Co Ξ q),
    (∀ g, ∃ t : ℝ, 0 ≤ t ∧ ptIp χ G e α α g = t) ∧ ((∀ g, ptIp χ G e α α g = 0) → α = 0)

theorem pairFacts_of_steps (h1 : BddInt) (h2 : CsBdd) (h3 : LevInv) (h4 : PtInv) (h5 : AdjInt) (h6 : PtD) (h7 : RapidBdd)
    (h8 : ZeroInt) (h9 : PtPos) : PairFacts := by
  intro E _ _ _ a ha μ _ U hU Ξ r χ G n e hD q
  have hv := h3 E a ha U hU Ξ r χ hD.one hD.tw
  have hc : ∀ α β : Co Ξ q, IsLev U Ξ α → IsLev U Ξ β → CInv (ptIp χ G e α β) := fun α β hα hβ => by
    rw [show ptIp χ G e α β = _ from funext (ptIp_eq χ G e α β)]
    exact CInv.sum _ fun I => (h4 E a χ _ G _ _).2.1 (hv q α hα _) (hv q β hβ _)
  refine ⟨fun α β hα hβ hr hm => ?_, fun α β hα hβ hs => ⟨?_, ?_⟩, fun α hα hi h0 => ?_, fun β η hβ hη hs => ?_⟩
  · obtain ⟨s, hs⟩ := hD.tw.1
    exact (h1 E a μ _ (hc α β hα hβ) (h2 E a _ (hc α β hα hβ) (.inr (h7 E a Ξ χ s hs G n e q α β hr hm)))).1
  · refine (h1 E a μ _ (hc α β hα hβ) (h2 E a _ (hc α β hα hβ) (.inl ?_))).1
    exact hs.imp fun R hR g hg => by simp [ptIp, hR _ g hg]
  · refine (h1 E a μ _ (hc β α hβ hα) (h2 E a _ (hc β α hβ hα) (.inl ?_))).1
    exact hs.imp fun R hR g hg => by simp [ptIp, hR _ g hg]
  · have hp := h9 E a Ξ χ G hD.adm n e hD.frame q α
    exact hp.2 (h8 E a μ _ (hc α α hα hα) hp.1 hi h0)
  · have hA := fun (J : Fin q → Fin n) (j : Fin n) => h5 E a μ Ξ r χ G hD.tw hD.adm (e j)
      (β (Matrix.vecCons (e j) fun i => e (J i))) (η fun i => e (J i)) (hv _ β hβ _) (hv _ η hη _)
      (hs.imp (fun h => h.imp fun R hR g hg => hR _ g hg) fun h => h.imp fun R hR g hg => hR _ g hg)
    simp only [pair, (h6 E a Ξ χ G n e q (smLie Ξ) β η _).1, (h6 E a Ξ χ G n e q (smAdj Ξ r) β η _).2]
    rw [integral_const_mul, integral_finset_sum _ fun J _ => integrable_finset_sum _ fun j _ => (hA J j).1,
      integral_finset_sum _ fun J _ => integrable_finset_sum _ fun j _ => (hA J j).2.1]
    congr 1
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [integral_finset_sum _ fun j _ => (hA J j).1, integral_finset_sum _ fun j _ => (hA J j).2.1]
    exact Finset.sum_congr rfl fun j _ => (hA J j).2.2

end UpperTheory.V.Lit.Geo.Pf
end
end

