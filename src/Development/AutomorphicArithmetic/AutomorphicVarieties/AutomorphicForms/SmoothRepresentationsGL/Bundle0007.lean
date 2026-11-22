import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import GroundTheory.GlobalFields.TateThesis.Bundle0008
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.PrSLocNe
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

section

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem pr_comm {S : Finset (HeightOneSpectrum (𝓞 E))} {x k : GL (Fin n) (Af E)} (hx : SuppIn S x)
    (hk : Away S k) : k * x = x * k := by
  refine cmp_ext fun w => ?_
  rw [map_mul, map_mul]
  by_cases h : w ∈ S
  · rw [hk w h, mul_one, one_mul]
  · rw [hx w h, mul_one, one_mul]

private theorem pr_sLoc (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) : pLoc E w (sLoc E w x) = x := by
  classical
  exact Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w x

private theorem pr_sLoc_ne {v w : HeightOneSpectrum (𝓞 E)} (h : v ≠ w) (x : w.adicCompletion E) :
    pLoc E v (sLoc E w x) = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) h x

private theorem pr_loc {S : Finset (HeightOneSpectrum (𝓞 E))} {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ S)
    {k : GL (Fin n) (w.adicCompletion E)} (hk : k ∈ GlobalTheory.LFun.KGL w n) : InKS S (locGL E n w k) := by
  have h1 : ∀ v, v ≠ w → cmp v (locGL E n w k) = 1 := fun v hv =>
    GlobalTheory.CuspRep.map_cornerGL_of_zero _ _ (pr_sLoc_ne hv) k
  have h2 : cmp w (locGL E n w k) = k :=
    GlobalTheory.CuspRep.map_cornerGL_of_hom _ _ (RingHom.id _) (pr_sLoc w) k
  refine ⟨fun v hv => h1 v fun e => hw (e ▸ hv), fun v => ?_⟩
  by_cases h : v = w
  · subst h; rw [h2]; exact hk
  · rw [h1 v h]; exact one_mem _

private theorem pr_fop {S : Finset (HeightOneSpectrum (𝓞 E))} {c : GL (Fin n) (Af E) →₀ ℂ}
    (hc : ∀ x ∈ c.support, SuppIn S x) {f : GA E n → ℂ} (hf : ∀ g k, InKS S k → f (g * finGL E n k) = f g)
    (g : GA E n) (k : GL (Fin n) (Af E)) (hk : InKS S k) : fop c f (g * finGL E n k) = fop c f g := by
  unfold fop
  refine Finsupp.sum_congr fun x hx => ?_
  rw [mul_assoc, ← map_mul, pr_comm (hc x hx) hk.1, map_mul, ← mul_assoc, hf _ _ hk]

private theorem pr_wh {f : GA E n → ℂ} {u : GA E n} (hf : ∀ g, f (g * u) = f g) (g : GA E n) :
    whittaker f (g * u) = whittaker f g := by
  unfold whittaker
  simp only [← mul_assoc, hf]

variable [IsTotallyReal E]

private theorem pr_conv {f : GA E n → ℂ} {k : GL (Fin n) (Af E)} (hf : ∀ g, f (g * finGL E n k) = f g)
    (α : Lie E n → ℂ) (g : GA E n) : conv f α (g * finGL E n k) = conv f α g := by
  unfold Af.Smo.conv
  congr 1
  funext x
  congr 1
  unfold chart
  split_ifs with h
  · rw [mul_assoc, ← TR.infGL_comm, ← mul_assoc, hf]
  · rfl

private theorem pr_mem (π : CuspSub E n) (c : GL (Fin n) (Af E) →₀ ℂ) {φ : TR.Sm E n} (hφ : φ ∈ π.V) :
    ∃ ψ ∈ π.V, ψ.1 = fop c φ.1 := by
  refine ⟨∑ x ∈ c.support, c x • TR.act (.fin x) φ,
    π.V.sum_mem fun x _ => π.V.smul_mem _ (π.stable _ _ hφ), ?_⟩
  funext g
  rw [Submodule.coe_sum, Finset.sum_apply]
  rfl

end

theorem UpperTheory.V.Af.Smo.pair :
    UpperTheory.V.Af.Smo.Seed → UpperTheory.V.Af.Smo.SetUp → UpperTheory.V.Af.Smo.KillP → UpperTheory.V.Af.Smo.Vanish → UpperTheory.V.Af.Smo.WhBasic → UpperTheory.V.Af.Smo.WhLin → UpperTheory.V.Af.Smo.ConvNice → UpperTheory.V.Af.Smo.EigOfSat → UpperTheory.V.Af.Smo.EigMap → UpperTheory.V.Af.Smo.Pair := by
  intro hSeed hSet hKill hVan hWB hWL hCN hES hEM E _ _ _ n hn π π' hc hc' hs
  obtain ⟨hN, φ, hφ, α, hα⟩ := hSeed E n π hc
  obtain ⟨hN', φ', hφ', α', hα'⟩ := hSeed E n π' hc'
  obtain ⟨S, B, hS, hK, hK'⟩ := hSet E n π π' hs φ hφ φ' hφ'
  obtain ⟨V, hV⟩ := (hN φ hφ).level
  obtain ⟨V', hV'⟩ := (hN' φ' hφ').level
  obtain ⟨c, H, hH, hc, hop⟩ := hKill E n hn S (V ⊓ V')

  have side : ∀ (σ : CuspSub E n), (∀ φ ∈ σ.V, Nice φ.1) → (∀ w ∉ S, σ.HasSat w (B w)) → ∀ φ ∈ σ.V,
      ∀ α : 𝓢(Lie E n, ℂ), conv (whittaker φ.1) α 1 = 1 → (∀ g k, InKS S k → φ.1 (g * finGL E n k) = φ.1 g) →
      (∀ g, ∀ u ∈ V ⊓ V', φ.1 (g * finGL E n u) = φ.1 g) →
      ∃ ψ ∈ σ.V, ∃ β : 𝓢(Lie E n, ℂ), Nice (conv ψ.1 β) ∧ (∀ w ∉ S, EigAt w (B w) (conv ψ.1 β)) ∧
        (∀ g k, InKS S k → conv ψ.1 β (g * finGL E n k) = conv ψ.1 β g) ∧
        ∀ p, InPS S p → whittaker (conv ψ.1 β) p = H p := by
    intro σ hN hsat φ hφ α hα hK hU
    obtain ⟨ψ, hψ, e⟩ := pr_mem σ c hφ
    obtain ⟨β, hβ⟩ := hop α
    have hK₁ : ∀ g k, InKS S k → ψ.1 (g * finGL E n k) = ψ.1 g := by
      rw [e]; exact pr_fop hc hK
    refine ⟨ψ, hψ, β, (hCN E n _ (hN ψ hψ) β).1, fun w hw => ?_, fun g k hk => pr_conv (fun g => hK₁ g k hk) _ g,
      fun p hp => ?_⟩
    · exact (hEM E n w (B w) _ (hES E n σ w (B w) (hsat w hw) ψ hψ
        fun g k hk => hK₁ g _ (pr_loc hw hk))).2.1 (hN ψ hψ) β
    · obtain ⟨b1, b2, b3⟩ := hWB E n _ (hN φ hφ)
      rw [(hCN E n _ (hN ψ hψ) β).2, e, ((hWL E n _ (hN φ hφ)).1 c).2,
        hβ _ b1 b2 b3 (fun g u hu => pr_wh (fun g => hU g u hu) g) p hp, hα, mul_one]
  obtain ⟨ψ, hψ, β, n1, e1, k1, w1⟩ := side π hN (fun w hw => (hS w hw).2.1) φ hφ α hα hK
    fun g u hu => hV g u hu.1
  obtain ⟨ψ', hψ', β', n2, e2, k2, w2⟩ := side π' hN' (fun w hw => (hS w hw).2.2) φ' hφ' α' hα' hK'
    fun g u hu => hV' g u hu.2
  obtain ⟨n3, w3⟩ := (hWL E n _ n1).2 _ n2
  refine ⟨ψ, hψ, ψ', hψ', β, β', sub_eq_zero.1 (hVan E n hn S B _ n3
    (fun w hw => ⟨(hS w hw).1, (hEM E n w (B w) _ (e1 w hw)).2.2 _ (e2 w hw)⟩) (fun g k hk => ?_) fun p hp => ?_),
    fun h0 => ?_⟩
  · rw [Pi.sub_apply, Pi.sub_apply, k1 g k hk, k2 g k hk]
  · rw [w3, Pi.sub_apply, w1 p hp, w2 p hp, sub_self]
  · have h1 : InPS S (1 : GA E n) := by
      refine ⟨fun i _ => ⟨by simp, fun j hj => ?_⟩, fun w _ => by rw [map_one, map_one]⟩
      exact Matrix.one_apply_ne hj.ne'
    have h2 := w1 1 h1
    rw [h0, hH] at h2
    simp [whittaker] at h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.PsiLoc
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem psiL_eq_one_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E) : psiL w x = 1 ↔ GroundTheory.Global.localAdelicChar E w x = 1 := by
  have h : psiL w x = (GroundTheory.Global.localAdelicChar E w x : ℂ) := rfl
  rw [h]
  exact Circle.coe_eq_one

private theorem exists_psiL_ne_one {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (z : w.adicCompletion E) (hz : z ∉ GroundTheory.Global.localInvDifferent w) :
    ∃ a ∈ w.adicCompletionIntegers E, psiL w (a * z) ≠ 1 := by
  by_contra hc
  refine hz ((GroundTheory.Global.forall_localAdelicChar_mul_eq_one_iff w z).1 fun a ha => ?_)
  rw [← psiL_eq_one_iff]
  by_contra h
  exact hc ⟨a, ha, h⟩

theorem UpperTheory.V.Af.Smo.psiLoc :
    UpperTheory.V.Af.Smo.PsiLoc := by
  intro E _ _
  refine ⟨fun w => ⟨?_, fun h => ?_⟩, ?_⟩
  · filter_upwards [(GroundTheory.Global.isOpen_localInvDifferent w).mem_nhds (zero_mem _)] with x hx
    exact (psiL_eq_one_iff w x).2 (GroundTheory.Global.localAdelicChar_eq_one_of_mem hx)
  · obtain ⟨z, hz⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w
      (WithZero.exp (FractionalIdeal.count E w ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 E)) E) + 1))
    obtain ⟨a, -, ha⟩ := exists_psiL_ne_one w z (by
      rw [GroundTheory.Global.mem_localInvDifferent_iff_valued, hz, WithZero.exp_le_exp]
      omega)
    exact ha (by rw [h]; rfl)
  · filter_upwards [FractionalIdeal.finite_factors (K := E) ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 E)) E)] with w hw
    refine ⟨fun x hx => (psiL_eq_one_iff w x).2 (GroundTheory.Global.localAdelicChar_eq_one_of_mem
      (GroundTheory.Global.mem_localInvDifferent_of_mem hx)), fun ϖ hϖ => ?_⟩
    have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
    have h0 : ϖ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hv
      exact WithZero.exp_ne_zero hv.symm
    obtain ⟨a, haO, ha⟩ := exists_psiL_ne_one w ϖ⁻¹ (by
      rw [GroundTheory.Global.mem_localInvDifferent_iff_valued, hw, map_inv₀, hv, ← WithZero.exp_neg,
        WithZero.exp_le_exp]
      omega)
    refine ⟨a * ϖ⁻¹, ?_, ha⟩
    rw [mul_left_comm, mul_inv_cancel₀ h0, mul_one]
    exact haO
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.RowStep
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem mul_rowM_apply {R : Type} [CommRing R] {n : ℕ} (m : Fin n) (ξ : Fin n → R)
    (q : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (q * rowM m ξ) i j
      = (if j = m then 0 else q i j) + q i m * (if j ≤ m then ξ j else 0) := by
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ m)]
  have hs : ∑ k ∈ Finset.univ.erase m, q i k * rowM m ξ k j = if j = m then 0 else q i j := by
    have hk1 : ∀ k ∈ Finset.univ.erase m,
        q i k * rowM m ξ k j = q i k * (1 : Matrix (Fin n) (Fin n) R) k j := by
      intro k hk
      have hkm : k ≠ m := Finset.ne_of_mem_erase hk
      simp [rowM, hkm]
    rw [Finset.sum_congr rfl hk1]
    split_ifs with hjm
    · apply Finset.sum_eq_zero
      intro k hk
      rw [Matrix.one_apply_ne (by rw [hjm]; exact Finset.ne_of_mem_erase hk), mul_zero]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        rw [Matrix.one_apply_ne hb, mul_zero]
      · intro hj
        exact absurd (Finset.mem_erase.mpr ⟨hjm, Finset.mem_univ j⟩) hj
  rw [hs, add_comm]
  congr 1
  by_cases hjm : j ≤ m
  · simp [rowM, hjm]
  · have hmj : m ≠ j := fun h => hjm (le_of_eq h.symm)
    simp [rowM, hjm, Matrix.one_apply_ne hmj]

theorem UpperTheory.V.Af.Smo.rowStep :
    UpperTheory.V.Af.Smo.RowStep := by
  unfold UpperTheory.V.Af.Smo.RowStep IsY
  intro R _ n m p s hp hs
  have key : ∀ i j, (p : Matrix (Fin n) (Fin n) R) i j
      = (if j = m then 0 else ((p * s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j)
        + ((p * s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i m
          * (if j ≤ m then (p : Matrix (Fin n) (Fin n) R) m j else 0) := by
    intro i j
    have h := mul_rowM_apply m ((p : Matrix (Fin n) (Fin n) R) m)
      ((p * s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j
    rw [← hs, ← Units.val_mul, inv_mul_cancel_right] at h
    exact h
  have hu : ((s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) m m
      * (p : Matrix (Fin n) (Fin n) R) m m = 1 := by
    have h := mul_rowM_apply m ((p : Matrix (Fin n) (Fin n) R) m)
      ((s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) m m
    rw [← hs, ← Units.val_mul, inv_mul_cancel] at h
    simpa using h.symm
  generalize ((s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) m m = t at hu
  generalize ((p * s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Q at key ⊢
  generalize (p : Matrix (Fin n) (Fin n) R) = P at key hu hp
  intro i hi
  rcases eq_or_lt_of_le hi with h | h
  · have him : i = m := Fin.ext h.symm
    rw [him]
    have k := key m m
    rw [if_pos rfl, if_pos le_rfl, zero_add] at k
    have hQ : Q m m = 1 := by linear_combination (-t) * k + (1 - Q m m) * hu
    refine ⟨hQ, fun j hj => ?_⟩
    have k2 := key m j
    rw [if_neg (ne_of_lt hj), if_pos (le_of_lt hj), hQ, one_mul] at k2
    linear_combination -k2
  · have hi1 : (m : ℕ) + 1 ≤ (i : ℕ) := h
    obtain ⟨hpi, hpj⟩ := hp i hi1
    have hmi : m < i := h
    have k := key i m
    rw [if_pos rfl, if_pos le_rfl, zero_add, hpj m hmi] at k
    have hQm : Q i m = 0 := by linear_combination (-Q i m) * hu - t * k
    constructor
    · have k2 := key i i
      rw [if_neg (ne_of_gt hmi), if_neg (not_le.mpr hmi), mul_zero, add_zero, hpi] at k2
      exact k2.symm
    · intro j hj
      have k2 := key i j
      rw [hpj j hj] at k2
      by_cases hjm : j = m
      · rw [hjm]
        exact hQm
      · rw [if_neg hjm, hQm, zero_mul, add_zero] at k2
        exact k2.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SchOfClosed
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.schOfClosed :
    UpperTheory.V.Af.Smo.SchOfClosed := by
  intro X _ _ _ A hA
  have b : Module.Basis (Fin (Module.finrank ℝ X)) ℝ X := Module.finBasis ℝ X
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank ℝ X) → (X →L[ℝ] ℝ), ∀ i x, c i x = b.repr x i :=
    ⟨fun i => LinearMap.toContinuousLinearMap (b.coord i), fun i x => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : Fin (Module.finrank ℝ X) → (ℂ →L[ℝ] (X →L[ℝ] ℂ)),
      ∀ i z v, L i z v = c i v • z :=
    ⟨fun i => ContinuousLinearMap.smulRightL ℝ X ℂ (c i), fun i z v => rfl⟩
  have hsm : ∀ n : ℕ, ∀ f ∈ A, ContDiff ℝ n f := by
    intro n
    induction n with
    | zero => intro f hf; exact contDiff_zero.2 (hA f hf).2.1.continuous
    | succ n ih =>
      intro f hf
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
      refine ⟨(hA f hf).2.1, by simp, ?_⟩
      rw [contDiff_clm_apply_iff]
      intro v
      exact ih _ ((hA f hf).2.2.1 v)
  have hinf : ∀ f ∈ A, ContDiff ℝ ∞ f := fun f hf => contDiff_infty.2 fun n => hsm n f hf
  have hx : ∀ x : X, ‖x‖ ≤ ∑ i, ‖b i‖ * ‖c i x‖ := by
    intro x
    calc ‖x‖ = ‖∑ i, b.repr x i • b i‖ := by rw [b.sum_repr]
      _ ≤ ∑ i, ‖b.repr x i • b i‖ := norm_sum_le _ _
      _ = ∑ i, ‖b i‖ * ‖c i x‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_smul, hc, mul_comm]
  have h0 : ∀ k : ℕ, ∀ f ∈ A, ∃ C, ∀ x, ‖x‖ ^ k * ‖f x‖ ≤ C := by
    intro k
    induction k with
    | zero =>
      intro f hf
      obtain ⟨C, hC⟩ := (hA f hf).1
      exact ⟨C, fun x => by simpa using hC x⟩
    | succ k ih =>
      intro f hf
      choose C hC using fun i => ih _ ((hA f hf).2.2.2 (c i))
      refine ⟨∑ i, ‖b i‖ * C i, fun x => ?_⟩
      calc ‖x‖ ^ (k + 1) * ‖f x‖ = ‖x‖ * (‖x‖ ^ k * ‖f x‖) := by ring
        _ ≤ (∑ i, ‖b i‖ * ‖c i x‖) * (‖x‖ ^ k * ‖f x‖) := by gcongr; exact hx x
        _ = ∑ i, ‖b i‖ * (‖x‖ ^ k * ‖(↑(c i x) : ℂ) * f x‖) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [norm_mul, Complex.norm_real]
            ring
        _ ≤ ∑ i, ‖b i‖ * C i := by
            gcongr with i
            exact hC i x
  have hd : ∀ n k : ℕ, ∀ f ∈ A, ∃ C, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
    intro n
    induction n with
    | zero =>
      intro k f hf
      obtain ⟨C, hC⟩ := h0 k f hf
      exact ⟨C, fun x => by rw [norm_iteratedFDeriv_zero]; exact hC x⟩
    | succ n ih =>
      intro k f hf
      obtain ⟨g, hg⟩ : ∃ g : Fin (Module.finrank ℝ X) → X → ℂ, ∀ i x, g i x = fderiv ℝ f x (b i) :=
        ⟨fun i x => fderiv ℝ f x (b i), fun _ _ => rfl⟩
      have hgA : ∀ i, g i ∈ A := by
        intro i
        have : g i = fun x => fderiv ℝ f x (b i) := funext (hg i)
        rw [this]
        exact (hA f hf).2.2.1 (b i)
      have hfd : fderiv ℝ f = fun x => ∑ i, L i (g i x) := by
        funext x
        ext v
        rw [ContinuousLinearMap.sum_apply]
        simp only [hL, hg, hc]
        conv_lhs => rw [← b.sum_repr v]
        rw [map_sum]
        simp only [map_smul]
      have hsum : iteratedFDeriv ℝ n (fun x => ∑ i, L i (g i x))
          = ∑ i, iteratedFDeriv ℝ n (fun y => L i (g i y)) :=
        iteratedFDeriv_sum (f := fun i y => L i (g i y)) (u := Finset.univ)
          (fun i _ => (L i).contDiff.comp (hsm n _ (hgA i)))
      choose C hC using fun i => ih k (g i) (hgA i)
      refine ⟨∑ i, ‖L i‖ * C i, fun x => ?_⟩
      rw [← norm_iteratedFDeriv_fderiv, hfd, hsum, Finset.sum_apply]
      calc ‖x‖ ^ k * ‖∑ i, iteratedFDeriv ℝ n (fun y => L i (g i y)) x‖
          ≤ ‖x‖ ^ k * ∑ i, ‖iteratedFDeriv ℝ n (fun y => L i (g i y)) x‖ := by
            gcongr
            exact norm_sum_le _ _
        _ ≤ ‖x‖ ^ k * ∑ i, ‖L i‖ * ‖iteratedFDeriv ℝ n (g i) x‖ := by
            gcongr with i
            exact (L i).norm_iteratedFDeriv_comp_left (hsm n _ (hgA i)).contDiffAt le_rfl
        _ = ∑ i, ‖L i‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (g i) x‖) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ ≤ ∑ i, ‖L i‖ * C i := by
            gcongr with i
            exact hC i x
  intro f hf
  exact ⟨⟨f, hinf f hf, fun k n => hd n k f hf⟩, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Seed
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.seed :
    UpperTheory.V.Af.Smo.WhBasic → UpperTheory.V.Af.Smo.SeedConv → UpperTheory.V.Af.Smo.Seed := by
  intro hW hS E _ _ _ n π hc
  have nice : ∀ φ ∈ π.V, Nice φ.1 := by
    intro φ hφ
    have hl := (π.cusp φ hφ).1.level
    rw [← Fb.map_carrier] at hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    refine ⟨ψ.2.1.continuous, exists_norm_le_of_mem_centralCuspForms (Fb.carrier_le_central π hc hψ),
      ψ.2.1.isLeftInvariant, ψ.2.2, ?_⟩
    let V : Subgroup (GL (Fin n) (Af E)) :=
      { carrier := {k | TR.finRep E n k (Fb.ofCusp E n ψ) = Fb.ofCusp E n ψ}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, Module.End.mul_apply, hb, ha]
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    exact ⟨⟨V, hl⟩, fun g v hv => congrFun (congrArg Subtype.val hv) g⟩
  refine ⟨nice, ?_⟩
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have N := nice φ hφ
  have hg : ∃ g, whittaker φ.1 g ≠ 0 := by
    by_contra h
    refine h0 (Subtype.ext (MultiplicityOne.eq_zero_of_whittaker_eq_zero N.cont N.left N.cusp ?_
      fun g => not_not.1 fun h' => h ⟨g, h'⟩))
    rw [Fb.finEmb_eq]
    exact N.level
  obtain ⟨g, hg⟩ := hg
  rw [← TR.infGL_mul_finGL g] at hg
  generalize GeneralLinearGroup.map (pInf E) g = y at hg
  generalize GeneralLinearGroup.map (pFin E) g = k at hg
  have hφ' := π.stable (.fin k) φ hφ
  refine ⟨_, hφ', hS E n _ (hW E n _ (nice _ hφ')).1 y ?_⟩
  have e : (TR.act (.fin k) φ).1 = fun x => φ.1 (x * finGL E n k) := rfl
  rw [e]
  simpa only [whittaker, mul_assoc] using hg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SeedConv
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem exists_schwartz_integral_eq_one {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure] (F : X → ℂ) (U : Set X) (x₀ : X)
    (hU : U ∈ 𝓝 x₀) (hF : ContinuousOn F U) (h0 : F x₀ ≠ 0) : ∃ α : 𝓢(X, ℂ), ∫ x, F x * α x ∂μ = 1 := by
  have hc : ContinuousAt (fun x => (F x / F x₀).re) x₀ :=
    Complex.continuous_re.continuousAt.comp ((hF.continuousAt hU).div_const _)
  have hp : ∀ᶠ x in 𝓝 x₀, 0 < (F x / F x₀).re :=
    hc.eventually (lt_mem_nhds (by simp [div_self h0]))
  obtain ⟨r, hr, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (Filter.inter_mem (interior_mem_nhds.2 hU) hp)
  let b : ContDiffBump x₀ := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hs : tsupport b = Metric.closedBall x₀ r := b.tsupport_eq
  have hs' : Function.support b = Metric.ball x₀ r := b.support_eq
  have hG : Continuous fun x => b x • (F x / F x₀) := by
    refine continuous_of_tsupport fun x hx => ?_
    have hx' : x ∈ Metric.closedBall x₀ r := hs ▸ tsupport_smul_subset_left _ _ hx
    exact b.continuous.continuousAt.smul ((hF.continuousAt (mem_interior_iff_mem_nhds.1 (hb hx').1)).div_const _)
  have hK : HasCompactSupport fun x => b x • (F x / F x₀) := b.hasCompactSupport.smul_right
  have hI : Integrable (fun x => b x • (F x / F x₀)) μ := hG.integrable_of_hasCompactSupport hK
  have hpos : 0 < ∫ x, (b x • (F x / F x₀)).re ∂μ := by
    refine (Complex.continuous_re.comp hG).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x₀)
      (hK.comp_left (g := Complex.re) rfl) (fun x => ?_) ?_
    · by_cases hx : b x = 0
      · simp [hx]
      · have hx' : x ∈ Metric.closedBall x₀ r := Metric.ball_subset_closedBall (hs' ▸ hx)
        have h1 : 0 < (F x / F x₀).re := (hb hx').2
        simpa using mul_nonneg b.nonneg h1.le
    · have h1 : b x₀ = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
      simp [h1, div_self h0]
  have hne : ∫ x, b x • (F x / F x₀) ∂μ ≠ 0 := by
    intro h
    have h2 := integral_re hI
    rw [h] at h2
    simp only [RCLike.re_to_complex, Complex.zero_re] at h2
    exact hpos.ne' h2
  set c := ∫ x, b x • (F x / F x₀) ∂μ with hc'
  have hd : ContDiff ℝ ∞ fun x => b x • ((F x₀)⁻¹ * c⁻¹) := b.contDiff.smul contDiff_const
  have hk : HasCompactSupport fun x => b x • ((F x₀)⁻¹ * c⁻¹) := b.hasCompactSupport.smul_right
  refine ⟨hk.toSchwartzMap hd, ?_⟩
  have e : ∀ x, F x * (hk.toSchwartzMap hd) x = (b x • (F x / F x₀)) * c⁻¹ := fun x => by
    change F x * (b x • ((F x₀)⁻¹ * c⁻¹)) = _
    simp only [Complex.real_smul, div_eq_mul_inv]
    ring
  simp only [e]
  rw [integral_mul_const, ← hc', mul_inv_cancel₀ hne]

theorem UpperTheory.V.Af.Smo.seedConv :
    UpperTheory.V.Af.Smo.ChartCont → UpperTheory.V.Af.Smo.SeedConv := by
  intro h E _ _ _ n W hW y hy
  haveI i1 : (volume : Measure (Rinf E)).IsAddHaarMeasure := inferInstance
  haveI i2 : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i3 : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  refine exists_schwartz_integral_eq_one volume (chart W 1) (invSet E n) (toL y.val) ?_ ?_ ?_
  · exact TR.isOpen_invSet.mem_nhds (TR.val_mem_invSet y)
  · exact (h E n W hW).1.comp (f := fun x => ((1 : GA E n), x)) (by fun_prop) fun x hx => ⟨trivial, hx⟩
  · rw [TR.chart_val, one_mul]
    exact hy
end

