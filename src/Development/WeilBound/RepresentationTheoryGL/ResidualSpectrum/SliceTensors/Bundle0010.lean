import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceA
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceB
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0494
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
import GroundTheory.PAdicHodge.ACrisBdR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermUnipotentIntegralVariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0365
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0505

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.EContJoin
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.SliceClasses

theorem E_lift {X Y : Type*} (L : ℝ → (X → ℂ) →ₗ[ℂ] (X → ℂ)) (L' : ℝ → (Y → ℂ) →ₗ[ℂ] (Y → ℂ))
    (hL0 : ∀ f, L 0 f = f) (hLL : ∀ s t f, L s (L t f) = L (t + s) f) (f₀ : X → ℂ)
    [FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun t => L t f₀))] (B : (X → ℂ) → (Y → ℂ))
    (hadd : ∀ v ∈ Submodule.span ℂ (Set.range fun t => L t f₀), ∀ w ∈ Submodule.span ℂ (Set.range fun t => L t f₀),
      B (v + w) = B v + B w)
    (hsmul : ∀ (a : ℂ), ∀ w ∈ Submodule.span ℂ (Set.range fun t => L t f₀), B (a • w) = a • B w)
    (c d : ℂ) (hB : ∀ t : ℝ, ∀ w ∈ Submodule.span ℂ (Set.range fun t => L t f₀),
      B (L t w) = Complex.exp (d * t) • L' t (B w))
    (F' : Y → ℂ) (hF' : F' ∈ Submodule.span ℂ (Set.range fun t => L' t (B f₀))) (hne : F' ≠ 0)
    (heig : ∀ t : ℝ, L' t F' = Complex.exp (c * t) • F') :
    ∃ F ∈ Submodule.span ℂ (Set.range fun t => L t f₀), F ≠ 0 ∧
      ∀ t : ℝ, L t F = Complex.exp ((c + d) * t) • F := by
  set W := Submodule.span ℂ (Set.range fun t => L t f₀) with hWdef
  have hf₀ : f₀ ∈ W := by
    have h0 : L 0 f₀ ∈ W := Submodule.subset_span ⟨0, rfl⟩
    rwa [hL0] at h0
  have hW : ∀ t, ∀ w ∈ W, L t w ∈ W := by
    intro t w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      rw [hLL]
      exact Submodule.subset_span ⟨u + t, rfl⟩
    | zero => rw [map_zero]; exact W.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact W.smul_mem a hx
  have hL : ∀ s t, ∀ w ∈ W, L s (L t w) = L t (L s w) := fun s t w _ => by rw [hLL, hLL, add_comm]
  have hB0 : B 0 = 0 := by
    have := hsmul 0 0 W.zero_mem
    rwa [zero_smul, zero_smul] at this
  have key : ∀ x ∈ Submodule.span ℂ (Set.range fun t => L' t (B f₀)), ∃ w ∈ W, B w = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      refine ⟨Complex.exp (-(d * t)) • L t f₀, W.smul_mem _ (Submodule.subset_span ⟨t, rfl⟩), ?_⟩
      rw [hsmul _ _ (Submodule.subset_span ⟨t, rfl⟩), hB t f₀ hf₀, smul_smul, ← Complex.exp_add, neg_add_cancel,
        Complex.exp_zero, one_smul]
    | zero => exact ⟨0, W.zero_mem, hB0⟩
    | add x y _ _ hx hy =>
      obtain ⟨v, hv, rfl⟩ := hx
      obtain ⟨w, hw, rfl⟩ := hy
      exact ⟨v + w, W.add_mem hv hw, hadd v hv w hw⟩
    | smul a x _ hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      exact ⟨a • v, W.smul_mem a hv, hsmul a v hv⟩
  obtain ⟨w₀, hw₀, hBw₀⟩ := key F' hF'
  exact eig_lift W L hL hW L' B hadd hsmul c d hB w₀ hw₀ (hBw₀ ▸ hne) (hBw₀ ▸ heig)

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def E_vol (E : Type) [Field E] [NumberField E] (N r : ℕ) : ℂ :=
  (((unipMeasure E N r).real (unipFundamentalDomain E N r) : ℝ) : ℂ)

omit [IsTotallyComplex E] in
theorem E_vol_ne (N r : ℕ) : E_vol E N r ≠ 0 := by
  have := JDict.vol_pos E N r
  unfold E_vol
  exact_mod_cast this.ne'

omit [IsTotallyComplex E] in
theorem E_ctn_eq {N : ℕ} (r : ℕ) (u : GA E N → ℂ) (g : GA E N) :
    An.ctn r u g = (E_vol E N r)⁻¹ * constantTerm r u g := rfl

omit [IsTotallyComplex E] in
theorem E_ct_eq {N : ℕ} (r : ℕ) (u : GA E N → ℂ) (g : GA E N) :
    constantTerm r u g = E_vol E N r * An.ctn r u g := by
  rw [E_ctn_eq, ← mul_assoc, mul_inv_cancel₀ (E_vol_ne N r), one_mul]

theorem E_cont_ctn {N : ℕ} (r : ℕ) {u : GA E N → ℂ} (hc : Continuous u)
    (hl : ∀ γ g, u (ratGL E N γ * g) = u g) : Continuous (An.ctn r u) := by
  have : BorelSpace (BlockIx N r → Ad E) := ⟨JDict.pi_eq_borel E N r⟩
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E N r
  have hfin : unipMeasure E N r (unipFundamentalDomain E N r) ≠ ⊤ := by
    obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := E) (n := N) (r := r)
    exact ((measure_mono hDC).trans_lt hC.measure_lt_top).ne
  have h := GlobalTheory.CompanionTheory.CuspL2.continuous_constTerm (unipMeasure E N r) hfin hK hcov hc hl
  refine continuous_const.mul ?_
  convert h using 2 with g
  simp only [constantTerm, GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip]

theorem E_cont_span {N : ℕ} (r : ℕ) {f : GA E N → ℂ} (hf : Continuous f) :
    ∀ w ∈ Submodule.span ℂ (Set.range fun t : ℝ => fun g => f (aT E N r t * g)), Continuous w := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    exact hf.comp (continuous_const.mul continuous_id)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact continuous_const.smul hx

def E_B {N : ℕ} {Y ι : Type*} [Fintype ι] (P : (ι → Ad E) → GA E N) (Q : ℝ → Y → GA E N) (κ : ℂ) (τs : Finset ℝ)
    (a : ℝ → ℂ) (f : GA E N → ℂ) (m : Y) : ℂ :=
  κ * ∑ t ∈ τs, a t * ∫ b, f (P b * Q t m) ∂(Measure.pi fun _ : ι => boxMeasure E)

omit [IsTotallyComplex E] in
theorem E_B_add {N : ℕ} {Y ι : Type*} [Fintype ι] {P : (ι → Ad E) → GA E N} (hP : Continuous P) (Q : ℝ → Y → GA E N)
    (κ : ℂ) (τs : Finset ℝ) (a : ℝ → ℂ) {f g : GA E N → ℂ} (hf : Continuous f) (hg : Continuous g) :
    E_B P Q κ τs a (f + g) = E_B P Q κ τs a f + E_B P Q κ τs a g := by
  funext m
  simp only [E_B, Pi.add_apply]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have hi : ∀ u : GA E N → ℂ, Continuous u →
      Integrable (fun b => u (P b * Q t m)) (Measure.pi fun _ : ι => boxMeasure E) := fun u hu =>
    integrable_box (hu.comp (hP.mul continuous_const))
  rw [← mul_add, ← integral_add (hi f hf) (hi g hg)]

omit [IsTotallyComplex E] in
theorem E_B_smul {N : ℕ} {Y ι : Type*} [Fintype ι] (P : (ι → Ad E) → GA E N) (Q : ℝ → Y → GA E N)
    (κ : ℂ) (τs : Finset ℝ) (a : ℝ → ℂ) (c : ℂ) (f : GA E N → ℂ) :
    E_B P Q κ τs a (c • f) = c • E_B P Q κ τs a f := by
  funext m
  simp only [E_B, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_const_mul]
  ring

omit [IsTotallyComplex E] in
theorem E_cont_join {n : ℕ} {S : Finset ℕ} (q : ℕ) :
    Continuous fun b : {x : PPos n S // ¬ IsTop q x} → Ad E => (parGL (joinPos (r := q) 0 b) : GA E n) := by
  refine continuous_parGL.comp (continuous_pi fun x => ?_)
  by_cases hx : IsTop q x
  · simp only [joinPos, dif_pos hx]
    exact continuous_const
  · simp only [joinPos, dif_neg hx]
    exact continuous_apply _

theorem E_pos_top {N p q : ℕ} (hpq : p < q) (x : PPos N {p, q}) (hx : ¬ IsTop q x) :
    (x.1.1 : ℕ) < p ∧ p ≤ (x.1.2 : ℕ) ∧ (x.1.2 : ℕ) < q := by
  obtain ⟨s, hs, h1, h2⟩ := x.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  have hx' : ¬ ((x.1.1 : ℕ) < q ∧ q ≤ (x.1.2 : ℕ)) := hx
  rcases hs with rfl | rfl <;> omega

theorem E_pos_bot {N p q : ℕ} (hpq : p < q) (x : PPos N {p, q}) (hx : ¬ IsTop p x) :
    p ≤ (x.1.1 : ℕ) ∧ (x.1.1 : ℕ) < q ∧ q ≤ (x.1.2 : ℕ) := by
  obtain ⟨s, hs, h1, h2⟩ := x.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  have hx' : ¬ ((x.1.1 : ℕ) < p ∧ p ≤ (x.1.2 : ℕ)) := hx
  rcases hs with rfl | rfl <;> omega

theorem E_exp_iff (hD : Dict) {N r : ℕ} (φ : Sm E N) (hφ : IsAutForm φ) (h0 : 0 < r) (h1 : r < N) (c : ℂ) :
    c ∈ Exp r φ.1 ↔ ∃ F ∈ Submodule.span ℂ (Set.range fun t : ℝ => fun g => An.ctn r φ.1 (aT E N r t * g)),
      F ≠ 0 ∧ ∀ (t : ℝ) g, F (aT E N r t * g) = Complex.exp (c * t) * F g := by
  have hd := (hD E N).2.2.2 φ hφ r h0 h1
  constructor
  · rintro ⟨F₀, hct, F, hF, hne, heig⟩
    obtain ⟨κ, -, rfl⟩ := hd.2 F₀ hct
    refine ⟨F, Submodule.span_le.2 ?_ hF, hne, heig⟩
    rintro _ ⟨t, rfl⟩
    have e : (fun g => κ * An.ctn r φ.1 (aT E N r t * g)) = κ • fun g => An.ctn r φ.1 (aT E N r t * g) := rfl
    simp only [e]
    exact Submodule.smul_mem _ κ (Submodule.subset_span ⟨t, rfl⟩)
  · rintro ⟨F, hF, hne, heig⟩
    exact ⟨An.ctn r φ.1, hd.1, F, hF, hne, heig⟩

end PositivityTheory.Rg.Rs.SliceClasses

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapD
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

def res (y : GA E (r + s)) : (GA E (r + s) → ℂ) →ₗ[ℂ] (GA E r × GA E s → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun m => lev (Ad E) r s m * y

theorem res_apply (y : GA E (r + s)) (F : GA E (r + s) → ℂ) (m : GA E r × GA E s) :
    res y F m = F (lev (Ad E) r s m * y) := rfl

structure Good (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) (f₁ : Sm E r →ₗ[ℂ] Sm E r)
    (f₂ : Sm E s →ₗ[ℂ] Sm E s) : Prop where
  hU₁ : IsStable U₁
  hU₂ : IsStable U₂
  hf₁ : ∀ o, ∀ ψ ∈ U₁, f₁ (act o ψ) = act o (f₁ ψ)
  hf₂ : ∀ o, ∀ ψ ∈ U₂, f₂ (act o ψ) = act o (f₂ ψ)

theorem good_id {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} (hU₁ : IsStable U₁) (hU₂ : IsStable U₂) :
    Good U₁ U₂ LinearMap.id LinearMap.id :=
  ⟨hU₁, hU₂, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

def IsInd (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) (F : GA E (r + s) → ℂ) : Prop :=
  (∀ (u : BlockIx (r + s) r → Ad E) x, F (unip u * x) = F x) ∧ ∀ k g, res (cf (r + s) k g) F ∈ tens2 U₁ U₂

def indSub (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) : Submodule ℂ (Sm E (r + s)) where
  carrier := {F | IsInd U₁ U₂ F.1}
  add_mem' := by
    intro F G hF hG
    refine ⟨fun u x => ?_, fun k g => ?_⟩
    · change F.1 _ + G.1 _ = F.1 x + G.1 x
      rw [hF.1, hG.1]
    · exact add_mem (hF.2 k g) (hG.2 k g)
  zero_mem' := by
    exact ⟨fun _ _ => rfl, fun _ _ => zero_mem _⟩
  smul_mem' := by
    intro c F hF
    refine ⟨fun u x => ?_, fun k g => ?_⟩
    · change c * F.1 _ = c * F.1 x
      rw [hF.1]
    · exact Submodule.smul_mem _ c (hF.2 k g)

theorem exists_dec (x : GA E (r + s)) :
    ∃ q : (BlockIx (r + s) r → Ad E) × (GA E r × GA E s) × Kinf E (r + s) × GL (Fin (r + s)) (Af E),
      x = unip q.1 * lev (Ad E) r s q.2.1 * cf (r + s) q.2.2.1 q.2.2.2 := by
  obtain ⟨u, m, k, g, h⟩ := exists_decomp x
  exact ⟨(u, m, k, g), h⟩

def ind (f₁ : Sm E r →ₗ[ℂ] Sm E r) (f₂ : Sm E s →ₗ[ℂ] Sm E s) : Module.End ℂ (GA E (r + s) → ℂ) :=
  LinearMap.pi fun x => LinearMap.proj (exists_dec x).choose.2.1 ∘ₗ tensOp f₁ f₂ ∘ₗ
    res (cf (r + s) (exists_dec x).choose.2.2.1 (exists_dec x).choose.2.2.2)

theorem cf_inv (a : ℕ) (k : Kinf E a) (g : GL (Fin a) (Af E)) : (cf a k g)⁻¹ = cf a k⁻¹ g⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [cf_mul, mul_inv_cancel, mul_inv_cancel, cf, map_one, map_one, map_one, mul_one]

theorem cf_one (a : ℕ) : cf a (1 : Kinf E a) 1 = 1 := by
  rw [cf, map_one, map_one, map_one, mul_one]

theorem D.unip_add' {R : Type} [CommRing R] {a r : ℕ} (x y : BlockIx a r → R) : unip (x + y) = unip x * unip y := by
  simp only [GlobalTheory.CompanionTheory.AffglAssembly.unip_eq_unipGL]
  exact GroundTheory.Automorphic.AutomorphicForm.unipGL_add x y

theorem D.indep {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F)
    {u u' : BlockIx (r + s) r → Ad E} {m m' : GA E r × GA E s} {k k' : Kinf E (r + s)} {g g' : GL (Fin (r + s)) (Af E)}
    (h : unip u * lev (Ad E) r s m * cf (r + s) k g = unip u' * lev (Ad E) r s m' * cf (r + s) k' g') :
    tensOp f₁ f₂ (res (cf (r + s) k g) F) m = tensOp f₁ f₂ (res (cf (r + s) k' g') F) m' := by
  obtain ⟨v, hv⟩ := lev_mul_unip m⁻¹ (-u + u')
  have hu : unip (-u) * unip u = (1 : GA E (r + s)) := by rw [← D.unip_add', neg_add_cancel, unip_zero]
  have e1 : cf (r + s) k g = unip v * lev (Ad E) r s (m⁻¹ * m') * cf (r + s) k' g' := by
    rw [map_mul, ← mul_assoc, ← hv, D.unip_add']
    calc cf (r + s) k g = lev (Ad E) r s m⁻¹ * (unip (-u) * (unip u * lev (Ad E) r s m * cf (r + s) k g)) := by
          rw [← mul_assoc (unip (-u)), ← mul_assoc (unip (-u)), hu, one_mul, ← mul_assoc, ← map_mul, inv_mul_cancel,
            map_one, one_mul]
      _ = _ := by rw [h]; simp only [mul_assoc]
  have e2 : unip v * lev (Ad E) r s (m⁻¹ * m') = cf (r + s) (k * k'⁻¹) (g * g'⁻¹) := by
    rw [← cf_mul, ← cf_inv, e1, mul_inv_cancel_right]
  obtain ⟨k₁, g₁, k₂, g₂, hm⟩ := levi_cf e2
  have e3 : res (cf (r + s) k g) F = fun z => res (cf (r + s) k' g') F (z.1 * cf r k₁ g₁, z.2 * cf s k₂ g₂) := by
    funext z
    obtain ⟨w, hw⟩ := lev_mul_unip z v
    rw [res_apply, res_apply, e1, ← mul_assoc, ← mul_assoc, hw, mul_assoc, mul_assoc, hF.1, ← mul_assoc, ← map_mul, hm]
    rfl
  rw [e3, tensOp_translate H.hU₁ H.hU₂ H.hf₁ H.hf₂ (hF.2 k' g')]
  have e4 : m' = (m.1 * cf r k₁ g₁, m.2 * cf s k₂ g₂) := by
    rw [← mul_inv_cancel_left m m', hm]
    rfl
  rw [e4]

theorem ind_apply {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F)
    (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    ind f₁ f₂ F (unip u * lev (Ad E) r s m * cf (r + s) k g) = tensOp f₁ f₂ (res (cf (r + s) k g) F) m := by
  have hq := (exists_dec (unip u * lev (Ad E) r s m * cf (r + s) k g)).choose_spec
  exact (D.indep H hF hq).symm

theorem ind_left {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F)
    (u : BlockIx (r + s) r → Ad E) (x : GA E (r + s)) : ind f₁ f₂ F (unip u * x) = ind f₁ f₂ F x := by
  obtain ⟨v, m, k, g, rfl⟩ := exists_decomp x
  rw [← mul_assoc, ← mul_assoc, ← D.unip_add', ind_apply H hF, ind_apply H hF]

theorem ind_levi {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F)
    (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    res (cf (r + s) k g) (ind f₁ f₂ F) = tensOp f₁ f₂ (res (cf (r + s) k g) F) := by
  funext m
  have := ind_apply H hF 0 m k g
  rw [unip_zero, one_mul] at this
  exact this

theorem isInd_rt {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {F : GA E (r + s) → ℂ}
    (hF : IsInd U₁ U₂ F) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    IsInd U₁ U₂ fun x => F (x * cf (r + s) k g) := by
  refine ⟨fun u x => by beta_reduce; rw [mul_assoc, hF.1], fun k' g' => ?_⟩
  convert hF.2 (k' * k) (g' * g) using 1
  funext m
  rw [res_apply, res_apply, mul_assoc, cf_mul]

theorem ind_rt {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F)
    (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (x : GA E (r + s)) :
    ind f₁ f₂ (fun y => F (y * cf (r + s) k g)) x = ind f₁ f₂ F (x * cf (r + s) k g) := by
  obtain ⟨v, m, k', g', rfl⟩ := exists_decomp x
  rw [ind_apply H (isInd_rt hF k g), mul_assoc _ (cf (r + s) k' g'), cf_mul, ind_apply H hF]
  refine congrArg (fun G => tensOp f₁ f₂ G m) (funext fun z => ?_)
  rw [res_apply, res_apply, mul_assoc, cf_mul]

theorem ext_res {F F' : GA E (r + s) → ℂ} (hF : ∀ (u : BlockIx (r + s) r → Ad E) x, F (unip u * x) = F x)
    (hF' : ∀ (u : BlockIx (r + s) r → Ad E) x, F' (unip u * x) = F' x)
    (e : ∀ k g, res (cf (r + s) k g) F = res (cf (r + s) k g) F') : F = F' := by
  funext x
  obtain ⟨v, m, k, g, rfl⟩ := exists_decomp x
  rw [mul_assoc, hF, hF']
  exact congrFun (e k g) m

theorem ind_id {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} (hU₁ : IsStable U₁) (hU₂ : IsStable U₂)
    {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F) : ind LinearMap.id LinearMap.id F = F := by
  refine ext_res (ind_left (good_id hU₁ hU₂) hF) hF.1 fun k g => ?_
  rw [ind_levi (good_id hU₁ hU₂) hF, tensOp_id (hF.2 k g)]

theorem finVec_rt {F : Sm E (r + s)} (hF : F ∈ finVec (cptRep E (r + s))) (k : Kinf E (r + s))
    (g : GL (Fin (r + s)) (Af E)) : rt E (r + s) (cf (r + s) k g) F ∈ finVec (cptRep E (r + s)) := by
  have h : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E (r + s) k F)) := hF
  change FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k' => cptRep E (r + s) k' (rt E (r + s) (cf (r + s) k g) F)))
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E (r + s) k F)).map
    (rt E (r + s) (finGL E (r + s) g))) (Submodule.span_le.2 ?_)
  rintro _ ⟨k', rfl⟩
  refine ⟨_, Submodule.subset_span ⟨k' * k, rfl⟩, Subtype.ext (funext fun x => ?_)⟩
  change F.1 (x * finGL E (r + s) g * infGL E (r + s) (Unitary.toUnits (k' * k))) =
    F.1 (x * infGL E (r + s) (Unitary.toUnits k') * cf (r + s) k g)
  rw [cf, mul_assoc x, ← infGL_comm, map_mul, map_mul]
  simp only [mul_assoc]

end PositivityTheory.Rg.Rs.InducedTensorMap

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceD
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.SliceClasses

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

theorem D_chart_left (F : GA E N → ℂ) (h g : GA E N) : chart (fun x => F (h * x)) g = chart F (h * g) := by
  funext x
  simp only [chart, mul_assoc]

def ltS (h : GA E N) : Sm E N →ₗ[ℂ] Sm E N where
  toFun F := ⟨fun g => F.1 (h * g), fun g => by rw [D_chart_left]; exact F.2 (h * g)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem ltS_apply (h : GA E N) (F : Sm E N) (g : GA E N) : (ltS h F).1 g = F.1 (h * g) := rfl

theorem ltS_act (h : GA E N) (o : Op E N) (F : Sm E N) : ltS h (act o F) = act o (ltS h F) := by
  cases o with
  | fin k =>
    refine Subtype.ext (funext fun g => ?_)
    change F.1 (h * g * finGL E N k) = F.1 (h * (g * finGL E N k))
    rw [mul_assoc]
  | cpt k =>
    refine Subtype.ext (funext fun g => ?_)
    change F.1 (h * g * _) = F.1 (h * (g * _))
    rw [mul_assoc]
  | lie X =>
    refine Subtype.ext (funext fun g => ?_)
    change lieD X F.1 (h * g) = lieD X (fun x => F.1 (h * x)) g
    simp only [lieD, D_chart_left]

theorem D_ct_smooth (r : ℕ) (φ : Sm E N) (hl : ∀ γ g, φ.1 (ratGL E N γ * g) = φ.1 g)
    (hlev : IsOpen {k | finRep E N k φ = φ}) :
    ∃ F : Sm E N, F.1 = An.ctn r φ.1 ∧ ∀ X, (lie E N X F).1 = An.ctn r (lie E N X φ).1 := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, hμ, hD, hint⟩ := JDict.exists_normed E N r
  obtain ⟨F, h1, h2⟩ := GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E N r φ hl hlev μ _ hμ hD
  have key : ∀ (f : GA E N → ℂ) g, ∫ x in unipFundamentalDomain E N r, f (unip x * g) ∂μ = An.ctn r f g := by
    intro f g
    rw [hint]
    simp only [An.ctn, constantTerm, GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip]
  exact ⟨F, funext fun g => (h1 g).trans (key _ g), fun X => funext fun g => (h2 X g).trans (key _ g)⟩

open Classical in

def ctSm (r : ℕ) (φ : Sm E N) : Sm E N := if h : An.ctn r φ.1 ∈ Sm E N then ⟨_, h⟩ else 0

theorem ctSm_val (r : ℕ) {φ : Sm E N} (hφ : IsAutForm φ) : (ctSm r φ).1 = An.ctn r φ.1 := by
  obtain ⟨F, hF, -⟩ := D_ct_smooth r φ hφ.left hφ.level
  have h : An.ctn r φ.1 ∈ Sm E N := hF ▸ F.2
  simp only [ctSm, dif_pos h]

theorem ctn_add (r : ℕ) {f g : GA E N → ℂ} (hf : Continuous f) (hg : Continuous g) :
    An.ctn r (f + g) = An.ctn r f + An.ctn r g := by
  funext x
  simp only [An.ctn, Pi.add_apply, constantTerm_add hf hg, mul_add]

theorem ctn_smul (r : ℕ) (c : ℂ) (f : GA E N → ℂ) : An.ctn r (c • f) = c • An.ctn r f := by
  funext x
  simp only [An.ctn, Pi.smul_apply, constantTerm_smul, smul_eq_mul]
  ring

theorem ctSm_act (r : ℕ) {φ : Sm E N} (hφ : IsAutForm φ) (o : Op E N) (hφ' : IsAutForm (act o φ)) :
    ctSm r (act o φ) = act o (ctSm r φ) := by
  obtain ⟨F, hF, hX⟩ := D_ct_smooth r φ hφ.left hφ.level
  have e : ctSm r φ = F := Subtype.ext ((ctSm_val r hφ).trans hF.symm)
  refine Subtype.ext ?_
  rw [ctSm_val r hφ', e]
  cases o with
  | fin k =>
    funext g
    change An.ctn r (fun x => φ.1 (x * finGL E N k)) g = F.1 (g * finGL E N k)
    rw [hF]
    simp only [An.ctn, constantTerm, mul_assoc]
  | cpt k =>
    funext g
    change An.ctn r (fun x => φ.1 (x * _)) g = F.1 (g * _)
    rw [hF]
    simp only [An.ctn, constantTerm, mul_assoc]
  | lie X => exact (hX X).symm

def Aop (N r : ℕ) (τs : Finset ℝ) (a : ℝ → ℂ) : Module.End ℂ (Sm E N) := ∑ t ∈ τs, a t • ltS (aT E N r t)

theorem Aop_apply (r : ℕ) (τs : Finset ℝ) (a : ℝ → ℂ) (F : Sm E N) (g : GA E N) :
    (Aop N r τs a F).1 g = ∑ t ∈ τs, a t * F.1 (aT E N r t * g) := by
  simp only [Aop, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply, ltS_apply, smul_eq_mul]

theorem Aop_act (r : ℕ) (τs : Finset ℝ) (a : ℝ → ℂ) (o : Op E N) (F : Sm E N) :
    Aop N r τs a (act o F) = act o (Aop N r τs a F) := by
  simp only [Aop, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, ltS_act]

theorem exists_strictHenselian_absolutely_closed_local_ring (V : Submodule ℂ (Sm E N)) (hV : ∀ φ ∈ V, IsAutForm φ) (r : ℕ) (τs : Finset ℝ) (a : ℝ → ℂ) :
    ∃ T : Sm E N →ₗ[ℂ] Sm E N, ∀ φ ∈ V, T φ = Aop N r τs a (ctSm r φ) := by
  let T₁ : V →ₗ[ℂ] Sm E N :=
    { toFun := fun φ => Aop N r τs a (ctSm r φ.1)
      map_add' := fun φ ψ => by
        have e : ctSm r (φ.1 + ψ.1) = ctSm r φ.1 + ctSm r ψ.1 := by
          refine Subtype.ext ?_
          rw [Submodule.coe_add, ctSm_val r (hV _ (V.add_mem φ.2 ψ.2)), ctSm_val r (hV _ φ.2),
            ctSm_val r (hV _ ψ.2)]
          exact ctn_add r (ContAut.continuous_of_isOpen_stab E N _ (hV _ φ.2).level)
            (ContAut.continuous_of_isOpen_stab E N _ (hV _ ψ.2).level)
        simp only [Submodule.coe_add, e, map_add]
      map_smul' := fun c φ => by
        have e : ctSm r (c • φ.1) = c • ctSm r φ.1 := by
          refine Subtype.ext ?_
          rw [Submodule.coe_smul, ctSm_val r (hV _ (V.smul_mem c φ.2)), ctSm_val r (hV _ φ.2)]
          exact ctn_smul r c _
        simp only [Submodule.coe_smul, e, map_smul, RingHom.id_apply] }
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T₁
  exact ⟨T, fun φ hφ => LinearMap.congr_fun hT ⟨φ, hφ⟩⟩

end PositivityTheory.Rg.Rs.SliceClasses

end
end

