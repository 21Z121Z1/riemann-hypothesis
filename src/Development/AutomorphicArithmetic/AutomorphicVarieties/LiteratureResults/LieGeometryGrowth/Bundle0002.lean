import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0001
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PerNat
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr
open scoped TensorProduct

private theorem hd_map {Γ M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (P : M →ₗ[ℂ] N)
    (b : List Γ → M) : hd (fun z => P (b z)) = fun z => P (hd b z) := by
  funext z
  simp only [hd, map_sum, map_zsmul]

private theorem zig_map {Γ V S S' : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    (G : Dr.Geo Γ V S d) (G' : Dr.Geo Γ V S' d) (f : S' → S) (P : ∀ q, G.Om q →ₗ[ℂ] G'.Om q)
    (ha : ∀ q γ w, P q (G.act q γ w) = G'.act q γ (P q w))
    (hD : ∀ q w, P (q + 1) (G.dOm q w) = G'.dOm q (P q w))
    (hi : ∀ c, P 0 (G.incl c) = G'.incl (c ∘ f)) (c : List Γ → S → Fin d → ℂ) (q : ℕ) :
    ∀ (k : ℕ) (u : List Γ → G.Om q), Zig G q k u c → Zig G' q k (fun z => P q (u z)) (fun z => c z ∘ f) := by
  induction q with
  | zero =>
    intro k u h z hz
    beta_reduce
    rw [h z hz, hi]
  | succ q ih =>
    rintro k u ⟨b, h1, h2, h3⟩
    refine ⟨fun z => P q (b z), fun γ z hz => ?_, fun z hz => ?_, ?_⟩
    · beta_reduce
      rw [h1 γ z hz, ha]
    · beta_reduce
      rw [← h2 z hz, hD]
    · rw [hd_map]
      exact ih _ _ h3

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private def pb (ho : IsOpen (cone E a)) (U U' : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (f : GL (Fin a) (Af E) ⧸ U' → GL (Fin a) (Af E) ⧸ U) (q : ℕ) : (geo ho U Ξ).Om q →ₗ[ℂ] (geo ho U' Ξ).Om q where
  toFun w := ⟨fun s => w.1 (f s), fun s => w.2 (f s)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem ev_rT {d : ℕ} (x : GL (Fin a) (Af E)) (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) :
    ev ((act (.fin x)).rTensor (Fin d → ℂ) m) g = ev m (g * finGL E a x) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v => rfl
  | add m m' h h' => simp only [map_add, Pi.add_apply, h, h']

private theorem rT_map' {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T A : Module.End ℂ W)
    (B : Module.End ℂ (Fin d → ℂ)) (h : A * T = T * A) (m : W ⊗[ℂ] (Fin d → ℂ)) :
    T.rTensor _ (TensorProduct.map A B m) = TensorProduct.map A B (T.rTensor _ m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul]
    congr 1
    exact (LinearMap.congr_fun h φ).symm

private theorem cpt_fin (k : Kinf E a) (x : GL (Fin a) (Af E)) :
    act (.cpt k) * act (.fin x) = act (.fin x) * act (E := E) (.cpt k) := by
  change rt E a _ * rt E a _ = rt E a _ * rt E a _
  rw [← map_mul, ← map_mul]
  exact congrArg _ (infGL_comm _ _)

private theorem rT_lie (Ξ : AlgRep E a) (x : GL (Fin a) (Af E)) (X : Lie E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (smLie Ξ X m) = smLie Ξ X ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) m) := by
  have h1 := rT_map' (act (.fin x)) (lie E a X) LinearMap.id (lie_rt_fin X x) m
  have h2 := rT_map' (act (.fin x)) LinearMap.id (Matrix.toLin' (Ξ.dmat X)) rfl m
  change (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (_ + _) = _ + _
  rw [map_add]
  exact congrArg₂ (· + ·) h1 h2

private theorem lev_fin {U U' : Subgroup (GL (Fin a) (Af E))} {x : GL (Fin a) (Af E)} (hx : ∀ u ∈ U', x⁻¹ * u * x ∈ U)
    (Ξ : AlgRep E a) {φ : Sm E a} (h : IsLevelFn U Ξ φ) : IsLevelFn U' Ξ (act (.fin x) φ) := by
  refine ⟨fun γ g => ?_, fun u hu => ?_, fun m hm => ?_⟩
  · change φ.1 (ratGL E a γ * g * finGL E a x) = φ.1 (g * finGL E a x)
    rw [mul_assoc, h.1]
  · refine Subtype.ext (funext fun g => ?_)
    have e : φ.1 (g * finGL E a x * finGL E a (x⁻¹ * u * x)) = φ.1 (g * finGL E a x) :=
      congrFun (congrArg Subtype.val (h.2.1 _ (hx u hu))) (g * finGL E a x)
    change φ.1 (g * finGL E a u * finGL E a x) = φ.1 (g * finGL E a x)
    rw [← e, mul_assoc, mul_assoc, ← map_mul, ← map_mul]
    congr 3
    group
  · have e : lie E a (oneL E a) (act (.fin x) φ) = act (.fin x) (lie E a (oneL E a) φ) :=
      LinearMap.congr_fun (lie_rt_fin (oneL E a) x) φ
    rw [e, h.2.2 m hm, map_smul]

end

theorem UpperTheory.V.Lit.Geo.perNat :
    PerNat := by
  intro E _ _ _ a U U' x hx Ξ q α hα
  refine ⟨⟨fun k X => ?_, fun X i hi => ?_, fun X => ?_⟩, ?_, fun c c' hc h => ?_⟩
  · change (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (α _) = smK Ξ k ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) (α X))
    rw [hα.equiv k X]
    exact rT_map' _ _ _ (cpt_fin k x) _
  · change (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (α X) = 0
    rw [hα.basic X i hi, map_zero]
  · change (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (α X) ∈ _
    have hm := hα.val X
    generalize α X = m at hm
    induction hm using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨φ, v, hφ, rfl⟩ := hy
      exact Submodule.subset_span ⟨_, v, lev_fin hx Ξ hφ, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul s y _ hy => rw [map_smul]; exact Submodule.smul_mem _ s hy
  · refine AlternatingMap.ext fun X => ?_
    change _ = (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (dCo (smLie Ξ) α X)
    simp only [dCo, AlternatingMap.alternatizeUncurryFin_apply, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
    exact (rT_lie Ξ x _ _).symm
  · obtain ⟨ho, w, hw, hz⟩ := h
    let f : GL (Fin a) (Af E) ⧸ U' → GL (Fin a) (Af E) ⧸ U := fun s =>
      Quotient.liftOn' s (fun y => ((y * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U)) fun y y' hy => by
        rw [QuotientGroup.leftRel_apply] at hy
        refine QuotientGroup.eq.2 ?_
        have := hx _ hy
        rwa [show (y * x)⁻¹ * (y' * x) = x⁻¹ * (y⁻¹ * y') * x by group]
    have hf : ∀ (g : GL (Fin a) (Af E)) s, f (g • s) = g • f s := fun g s => by
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
      change ((g * y * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) = ((g * (y * x) : GL (Fin a) (Af E)) : _ ⧸ U)
      rw [mul_assoc]
    have hc' : c' = fun z => c z ∘ f := by
      funext z s
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
      exact hc z y
    refine ⟨ho, pb ho U U' Ξ f q w, fun g y X => ?_, ?_⟩
    · change w.1 ((y * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) _ _ =
        Ξ.mat g *ᵥ ev ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) (α X)) _
      rw [ev_rT, mul_assoc, ← map_mul]
      exact hw g (y * x) X
    · rw [hc']
      refine zig_map (geo ho U Ξ) (geo ho U' Ξ) f (pb ho U U' Ξ f) (fun q γ w => ?_) (fun q w => rfl) (fun c => rfl) c q 0 _ hz
      refine Subtype.ext (funext fun s => funext fun p => ContinuousAlternatingMap.ext fun v => ?_)
      change _ *ᵥ w.1 ((geo ho U Ξ).σ γ⁻¹ (f s)) _ _ = _ *ᵥ w.1 (f ((geo ho U' Ξ).σ γ⁻¹ s)) _ _
      rw [geo_σ, geo_σ, hf]
      rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullDefs
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open scoped ContDiff TensorProduct

namespace UpperTheory.V.Lit.Geo

section Abs

variable {V' V F : Type} [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def pb (H : V' → V) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V') : V' [⋀^Fin q]→L[ℝ] F :=
  (w (H p)).compContinuousLinearMap (fderiv ℝ H p)

theorem pb_apply (H : V' → V) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V') (v : Fin q → V') :
    pb H w p v = w (H p) fun i => fderiv ℝ H p (v i) := rfl

def flow (W : V → V) (t : ℝ) (p : V) : V := p + t • W p

def hk (W : V → V) (t : ℝ) {q : ℕ} (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p : V) : V [⋀^Fin q]→L[ℝ] F :=
  ((w (flow W t p)).curryLeft (W p)).compContinuousLinearMap (fderiv ℝ (flow W t) p)

theorem hk_apply (W : V → V) (t : ℝ) {q : ℕ} (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p : V) (v : Fin q → V) :
    hk W t w p v = w (flow W t p) (Matrix.vecCons (W p) fun i => fderiv ℝ (flow W t) p (v i)) := rfl

def hom (W : V → V) {q : ℕ} (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p : V) : V [⋀^Fin q]→L[ℝ] F :=
  ∫ t in (0 : ℝ)..1, hk W t w p

def IsField (Y : Set V) (W : V → V) : Prop :=
  ContDiffOn ℝ ∞ W Y ∧ ∀ p ∈ Y, ∀ t ∈ Set.Icc (0 : ℝ) 1, flow W t p ∈ Y

end Abs

section Om

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} (G : Dr.Geo Γ V S d)

structure IsFlow (W : S → V → V) : Prop where
  field : ∀ s, IsField G.Y (W s)
  equiv : ∀ γ s, ∀ p ∈ G.Y, W (G.σ γ s) (G.ρ γ p) = G.ρ γ (W s p)
  homog : ∀ s (t : ℝ), 0 < t → ∀ p ∈ G.Y, W s (t • p) = t • W s p

theorem isFlow_zero : IsFlow G 0 :=
  ⟨fun _ => ⟨contDiffOn_const, fun p hp t _ => by simpa [flow] using hp⟩, fun _ _ _ _ => by simp, fun _ _ _ _ _ => by simp⟩

open Classical in

def toOm {q : ℕ} (z : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) : G.Om q :=
  if h : ∀ s, ContDiffOn ℝ ∞ (z s) G.Y then
    ⟨fun s => G.Y.indicator (z s), fun s =>
      ⟨(h s).congr fun _ hp => Set.indicator_of_mem hp _, fun _ hp => Set.indicator_of_notMem hp _⟩⟩
  else 0

theorem toOm_apply {q : ℕ} {z : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)} (h : ∀ s, ContDiffOn ℝ ∞ (z s) G.Y) (s : S) {p : V}
    (hp : p ∈ G.Y) : (toOm G z).1 s p = z s p := by
  rw [toOm, dif_pos h]
  exact Set.indicator_of_mem hp _

def pbOm (W : S → V → V) {q : ℕ} (w : G.Om q) : G.Om q := toOm G fun s => pb (flow (W s) 1) (w.1 s)

def homOm (W : S → V → V) {q : ℕ} (w : G.Om (q + 1)) : G.Om q := toOm G fun s => hom (W s) (w.1 s)

structure Good {q : ℕ} (w : G.Om q) : Prop where
  inv : ∀ γ, G.act q γ w = w
  basic : ∀ s, RadBasic G.Y (w.1 s)
  dbasic : ∀ s, RadBasic G.Y ((G.dOm q w).1 s)

end Om

section Ad

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

structure IsFld (U : Subgroup (GL (Fin a) (Af E))) (Y : GA E a → Herm E a) (C : ℝ) : Prop where
  sm : ∀ i j w, ∃ φ : Sm E a, (∀ g, φ.1 g = (Y g).1 i j w) ∧ BddDer φ
  left : ∀ γ t g, Y (ratGL E a γ * splitCentre E a t * g) = Y g
  cpt : ∀ (k : Kinf E a) g, adHerm k (Y (g * infGL E a (Unitary.toUnits k))) = Y g
  lev : ∀ u ∈ U, ∀ g, Y (g * finGL E a u) = Y g
  root : ∀ g (t : ℝ), |t| ≤ 1 → ∃ h : GL (Fin a) (Cinf E), h.val * star h.val = 1 + t • (Y g).1 ∧
    ‖toL h.val‖ ≤ C ∧ ‖toL (h⁻¹).val‖ ≤ C

theorem IsStep.fld {U : Subgroup (GL (Fin a) (Af E))} {f : GA E a → ℝ} {Y : GA E a → Herm E a} {C c f₀ : ℝ}
    (h : IsStep U f Y C c f₀) : IsFld U Y C := ⟨h.Y_sm, h.Y_left, h.Y_cpt, h.Y_lev, h.root⟩

theorem IsFld.neg {U : Subgroup (GL (Fin a) (Af E))} {Y : GA E a → Herm E a} {C : ℝ} (h : IsFld U Y C) :
    IsFld U (-Y) C where
  sm i j w := by
    obtain ⟨φ, h1, h2⟩ := h.sm i j w
    refine ⟨-φ, fun g => congrArg Neg.neg (h1 g), fun X l => ?_⟩
    obtain ⟨B, hB⟩ := h2 X l
    exact ⟨B, fun g => by rw [map_neg]; exact (norm_neg _).trans_le (hB g)⟩
  left γ t g := congrArg Neg.neg (h.left γ t g)
  cpt k g := by
    have e := congrArg Subtype.val (h.cpt k g)
    refine Subtype.ext ?_
    change k.1 * (-(Y (g * infGL E a (Unitary.toUnits k))).1) * star k.1 = -(Y g).1
    rw [mul_neg, neg_mul, ← e]
    rfl
  lev u hu g := congrArg Neg.neg (h.lev u hu g)
  root g t ht := by
    obtain ⟨x, h1, h2⟩ := h.root g (-t) (by rwa [abs_neg])
    exact ⟨x, by rw [h1, neg_smul]; exact congrArg (1 + ·) (smul_neg t (Y g).1).symm, h2⟩

def FCorr (U : Subgroup (GL (Fin a) (Af E))) (Y : GA E a → Herm E a) (W : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a) : Prop :=
  ∀ (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)),
    W (x : GL (Fin a) (Af E) ⧸ U) (sand g (hOne E a)) = sand g (hv (Y (infGL E a g * finGL E a x)))

theorem FCorr.neg {U : Subgroup (GL (Fin a) (Af E))} {Y : GA E a → Herm E a}
    {W : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a} (h : FCorr U Y W) : FCorr U (-Y) (-W) := fun g x => by
  simp only [Pi.neg_apply, map_neg, h g x]

def Bd {Ξ : AlgRep E a} {q : ℕ} (α : Co Ξ q) (g : GA E a) (M : ℝ) : Prop :=
  ∀ X : Fin q → Herm E a, ‖ev (α X) (retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ M * ∏ i, ‖hv (X i)‖

theorem Bd.mono {Ξ : AlgRep E a} {q : ℕ} {α : Co Ξ q} {g : GA E a} {M M' : ℝ} (h : Bd α g M) (hM : M ≤ M') : Bd α g M' :=
  fun X => (h X).trans (mul_le_mul_of_nonneg_right hM (Finset.prod_nonneg fun _ _ => norm_nonneg _))

theorem Bd.sub {Ξ : AlgRep E a} {q : ℕ} {α β : Co Ξ q} {g : GA E a} {M M' : ℝ} (h : Bd α g M) (h' : Bd β g M') :
    Bd (α - β) g (M + M') := fun X => by
  rw [AlternatingMap.sub_apply, map_sub, Pi.sub_apply, add_mul]
  exact (norm_sub_le _ _).trans (add_le_add (h X) (h' X))

end Ad

end UpperTheory.V.Lit.Geo
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem qht_le (g : GA E a) (γ : GL (Fin a) E) :
    qht g ≤ height (K := E) (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1) :=
  ciInf_le ⟨1, by rintro _ ⟨δ, rfl⟩; exact one_le_height _⟩ γ

private theorem one_le_qht (g : GA E a) : 1 ≤ qht g := le_ciInf fun _ => one_le_height _

private theorem retract_left (γ : GL (Fin a) E) (t : ℝ) (g : GA E a) :
    (retractOne (ratGL E a γ * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1 := by
  let y : KernelIndexFullLattice.G1 E a := ⟨ratGL E a γ, Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩⟩
  change (retractOne ((y : GA E a) * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = _
  rw [mul_assoc, retractOne_coe_mul, retractOne_mul, KernelIndexFullLattice.splitEq_holds E a t, retractOne_centralSection, one_mul]
  rfl

private theorem qht_left (γ : GL (Fin a) E) (t : ℝ) (g : GA E a) :
    qht (ratGL E a γ * splitCentre E a t * g) = qht g := by
  unfold qht
  rw [retract_left]
  refine Eq.trans ?_ ((Equiv.mulRight γ).iInf_comp
    (g := fun δ : GL (Fin a) E => height (K := E) (ratGL E a δ * (retractOne g : KernelIndexFullLattice.G1 E a).1)))
  refine congrArg _ (funext fun δ => ?_)
  rw [Equiv.coe_mulRight, map_mul, mul_assoc]

private theorem exists_split (g : GA E a) : ∃ t : ℝ, splitCentre E a t * g = (retractOne g : KernelIndexFullLattice.G1 E a).1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨0, Units.ext (Subsingleton.elim _ _)⟩
  have h1 : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have h2 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  refine ⟨Real.log ((Reduction.detModule E a g)⁻¹).1 / (a * Module.finrank ℚ E), ?_⟩
  rw [KernelIndexFullLattice.splitEq_holds E a, coe_retractOne, ← centralSection_inv_mul_comm,
    ← map_inv (Reduction.centralSection E a)]
  refine congrArg (fun s => Reduction.centralSection E a s * g) (Subtype.ext ?_)
  change Real.exp _ = _
  rw [mul_div_cancel₀ _ (mul_pos h1 h2).ne', Real.exp_log ((Reduction.detModule E a g)⁻¹).2]

private theorem qht_mul {C : Set (GA E a)} (hC : IsCompact C) :
    ∃ B : ℝ, ∀ g : GA E a, ∀ h ∈ C, qht (g * h) ≤ B * qht g := by
  obtain ⟨M, hM⟩ := exists_height_le_of_isCompact (K := E) (n := a)
    (hC.image (continuous_subtype_val.comp (continuous_retractOne (K := E) (n := a))))
  have hc : 0 < heightConst E a := one_pos.trans_le one_le_heightConst
  refine ⟨heightConst E a * M, fun g h hh => ?_⟩
  have hm := hM _ ⟨h, hh, rfl⟩
  have hM0 : 0 < M := (height_pos _).trans_le hm
  rw [← div_le_iff₀' (mul_pos hc hM0)]
  refine le_ciInf fun γ => ?_
  rw [div_le_iff₀' (mul_pos hc hM0)]
  refine (qht_le _ γ).trans ?_
  rw [retractOne_mul, Subgroup.coe_mul, ← mul_assoc, mul_right_comm]
  exact (height_mul_le _ _).trans (mul_le_mul_of_nonneg_left hm (mul_pos hc (height_pos _)).le)

private theorem qht_proper (R : ℝ) : ∃ C : Set (GA E a), IsCompact C ∧
    ∀ g : GA E a, qht g ≤ R → ∃ γ t, ratGL E a γ * splitCentre E a t * g ∈ C := by
  obtain ⟨c, N, hc, h⟩ := UpperTheory.adelicNorm_vecMul_ge_of_height E a
  have hR : 0 < max 1 R + 1 := by positivity
  obtain ⟨C, hC, hC'⟩ := Reduction.exists_isCompact_forall_of_pos_le_height (K := E) (n := a)
    (ε := (c * (max 1 R + 1) ^ N)⁻¹) (by positivity)
  refine ⟨C, hC, fun g hg => ?_⟩
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt (hg.trans_lt ((le_max_right 1 R).trans_lt (lt_add_one _)))
  obtain ⟨t, ht⟩ := exists_split g
  obtain ⟨_, ⟨δ, rfl⟩, x, hx, e⟩ := hC' (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1)
    (mul_mem (Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩) (retractOne g).2) fun v hv => by
      rw [inv_le_iff_one_le_mul₀' (by positivity)]
      have h0 := h (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1) v hv
      have hp : 0 ≤ Reduction.height (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1) v := by
        by_contra hn
        have : 0 ≤ c * height (K := E) (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1) ^ N := by
          have := height_pos (K := E) (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1)
          positivity
        nlinarith [not_le.1 hn]
      exact h0.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (height_pos _).le hγ.le N) hc.le) hp)
  refine ⟨δ⁻¹ * γ, t, ?_⟩
  have e' : ratGL E a δ * x = ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1 := e
  rw [mul_assoc, ht, map_mul, mul_assoc, ← e', map_inv, inv_mul_cancel_left]
  exact hx

end UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.qhtFacts :
    QhtFacts := by
  intro E _ _ _ a
  exact ⟨one_le_qht, qht_left, fun _ hC => qht_mul hC, qht_proper⟩
end

