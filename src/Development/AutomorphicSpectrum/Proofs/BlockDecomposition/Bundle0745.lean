import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1731
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0742
import Development.AutomorphicSpectrum.Proofs.HermitianForms.Imports
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightHermitianDerivation
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0739
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0387
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0584
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTopology
section
open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open PositivityTheory.RgEis ResidueKilled.Tr PositivityTheory.Rg.SwEis
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SwEisTop

theorem ext_mul_eq {G : Type} [Group G] (K P : Subgroup G) (f : G → ℝ)
    (hadd : ∀ p ∈ P, ∀ q ∈ P, f (p * q) = f p + f q) (hK : ∀ p ∈ P, p ∈ K → f p = 0)
    {p k : G} (hp : p ∈ P) (hk : k ∈ K) : ext K P f (p * k) = f p := by
  unfold ext
  have h : ∃ k' : K, p * k * (k' : G)⁻¹ ∈ P := ⟨⟨k, hk⟩, by simpa using hp⟩
  rw [dif_pos h]
  have h1 := h.choose_spec
  have hm : k * (h.choose : G)⁻¹ ∈ P := by
    have := P.mul_mem (P.inv_mem hp) h1
    simpa [mul_assoc] using this
  have hmK : k * (h.choose : G)⁻¹ ∈ K := K.mul_mem hk (K.inv_mem h.choose.2)
  rw [mul_assoc, hadd p hp _ hm, hK _ hm hmK, add_zero]

theorem absA_pos' {D : D7} (u : (AE D)ˣ) : 0 < absA D u := by
  have h : absA D u * absA D u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact pos_iff_ne_zero.mpr fun h0 => by simp [h0] at h

section Gen

variable {E R : Type} [Field E] [CommRing R] (A : Ad E R) (ε : ℤˣ) {ι : Type} [Fintype ι] [DecidableEq ι] (S : Set ι)

theorem uH_mul (hmul : ∀ p ∈ stab R ((Sum.inl '' S : Set (ι ⊕ ι))), ∀ q ∈ stab R ((Sum.inl '' S : Set (ι ⊕ ι))),
      bdet ((Sum.inl '' S : Set (ι ⊕ ι))) (p * q) = bdet ((Sum.inl '' S : Set (ι ⊕ ι))) p * bdet ((Sum.inl '' S : Set (ι ⊕ ι))) q)
    (hlg : ∀ x y, A.lg (x * y) = A.lg x + A.lg y)
    (hk0 : ∀ p ∈ stab R ((Sum.inl '' S : Set (ι ⊕ ι))), p ∈ A.kGL (ι ⊕ ι) → A.lg (bdet ((Sum.inl '' S : Set (ι ⊕ ι))) p) = 0)
    {p k : A.U ε ι} (hp : p ∈ A.uQ ε S) (hk : k ∈ A.uK ε ι) :
    A.uH ε S (p * k) = A.lg (bdet ((Sum.inl '' S : Set (ι ⊕ ι))) p.1) :=
  ext_mul_eq (A.uK ε ι) (A.uQ ε S) (fun p => A.lg (bdet ((Sum.inl '' S : Set (ι ⊕ ι))) p.1))
    (fun p hp q hq => by
      show A.lg (bdet _ (p.1 * q.1)) = _
      exact (congrArg A.lg (hmul p.1 hp q.1 hq)).trans (hlg _ _))
    (fun p hp hk => hk0 _ hp hk) hp hk

end Gen

theorem exp_uH_eq (hDict : Dict) (hBd : BdetLaw) {D : D7} {χ : (AE D)ˣ →* Circle} {n : ℕ}
    (hGood : (adCM D.sp.cm.sig χ).Good) (Ψ : GlobalTheory.StdUnn.G D n ≃ₜ* UD D χ n)
    (hP : ∀ g, g ∈ GlobalTheory.StdUnn.P D n ↔ Ψ g ∈ (adCM D.sp.cm.sig χ).uQ (-1) (Set.univ : Set (Fin n)))
    (hK : ∀ g, g ∈ GlobalTheory.StdUnn.K D n ↔ Ψ g ∈ (adCM D.sp.cm.sig χ).uK (-1) (Fin n))
    (hdet : ∀ (g : GlobalTheory.StdUnn.G D n) (a : GL (Fin n) (AE D)), GlobalTheory.StdUnn.blkA (GlobalTheory.StdUnn.mat g) = a.1 →
      bdet (Sum.inl '' (Set.univ : Set (Fin n))) (Ψ g).1 = Matrix.GeneralLinearGroup.det a)
    (hI : Iwa ((adCM D.sp.cm.sig χ).uQ (-1) (Set.univ : Set (Fin n))) ((adCM D.sp.cm.sig χ).uK (-1) (Fin n)))
    {H : GlobalTheory.StdUnn.G D n → ℝ≥0} (hH : GlobalTheory.StdUnn.IsHeight H) (x : GlobalTheory.StdUnn.G D n) :
    Real.exp ((adCM D.sp.cm.sig χ).uH (-1) Set.univ (Ψ x)) = (H x : ℝ) := by
  have hBd' := hBd _ _ (adCM D.sp.cm.sig χ) hGood.toGoodL (Fin n ⊕ Fin n) (Sum.inl '' Set.univ)
  obtain ⟨p, hp, k, hk, e⟩ := hI (Ψ x)
  have h1 := uH_mul (adCM D.sp.cm.sig χ) (-1) (Set.univ : Set (Fin n)) hBd'.2.1 hGood.lgmul hBd'.2.2.2.2.1 hp hk
  rw [← e] at h1
  have hp₀ : Ψ.symm p ∈ GlobalTheory.StdUnn.P D n := (hP _).2 (by simpa using hp)
  have hk₀ : Ψ.symm k ∈ GlobalTheory.StdUnn.K D n := (hK _).2 (by simpa using hk)
  have hx : x = Ψ.symm p * Ψ.symm k := by rw [← map_mul, ← e, ContinuousMulEquiv.symm_apply_apply]
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hp₀
  have h2 := hdet _ a ha
  rw [ContinuousMulEquiv.apply_symm_apply] at h2
  have h3 := hH _ hp₀ a ha _ hk₀
  rw [← hx] at h3
  have h4 : (adCM D.sp.cm.sig χ).lg (Matrix.GeneralLinearGroup.det a) =
      Real.log (absA D (Matrix.GeneralLinearGroup.det a)) := by
    have e5 := (hDict D.host.F D.host.E).2.2.2.2 (Matrix.GeneralLinearGroup.det a)
    show Real.log _ = _
    rw [e5]
  rw [h1, h2, h4, h3, Real.exp_log (by exact_mod_cast absA_pos' _)]

theorem law_div {D : D7} {n : ℕ} {χ : (AE D)ˣ →* Circle} {G' : Type} [Group G'] [TopologicalSpace G']
    (Ψ : GlobalTheory.StdUnn.G D n ≃ₜ* G') (P' : Subgroup G') (η : G' → ℝ) (c : G' → ℂ)
    (hP : ∀ g, g ∈ GlobalTheory.StdUnn.P D n ↔ Ψ g ∈ P') (hleft : ∀ p ∈ P', ∀ g, η (p * g) = η p + η g)
    (hc : ∀ (g : GlobalTheory.StdUnn.G D n) (a : GL (Fin n) (AE D)), GlobalTheory.StdUnn.blkA (GlobalTheory.StdUnn.mat g) = a.1 →
      c (Ψ g) = χ (Matrix.GeneralLinearGroup.det a))
    {H : GlobalTheory.StdUnn.G D n → ℝ≥0} (hH : GlobalTheory.StdUnn.IsHeight H) (hexp : ∀ x, Real.exp (η (Ψ x)) = (H x : ℝ))
    {s₁ : ℂ} {φ : GlobalTheory.StdUnn.G D n → ℂ} (hφ : GlobalTheory.StdUnn.IsSection χ s₁ φ) :
    ∀ q ∈ GlobalTheory.StdUnn.P D n, ∀ g, φ (q * g) * Complex.exp (-(s₁ + (n : ℂ) / 2) * η (Ψ (q * g))) =
      c (Ψ q) * (φ g * Complex.exp (-(s₁ + (n : ℂ) / 2) * η (Ψ g))) := by
  intro q hq g
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hq
  have hq' := (hP q).1 hq
  have h3 : η (Ψ q) = Real.log (absA D (Matrix.GeneralLinearGroup.det a)) := by
    have h := hH q hq a ha 1 (one_mem _)
    rw [mul_one] at h
    rw [← Real.log_exp (η (Ψ q)), hexp q, h]
  rw [hφ.1 q hq a ha g, map_mul, hleft _ hq' _, h3, hc q a ha, npow_eq_exp (absA_pos' _)]
  have key : Complex.exp (((Real.log (absA D (Matrix.GeneralLinearGroup.det a)) : ℝ) : ℂ) * (s₁ + (n : ℂ) / 2)) *
      Complex.exp (-(s₁ + (n : ℂ) / 2) * ((Real.log (absA D (Matrix.GeneralLinearGroup.det a)) + η (Ψ g) : ℝ) : ℂ)) =
      Complex.exp (-(s₁ + (n : ℂ) / 2) * (η (Ψ g) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination ((χ (Matrix.GeneralLinearGroup.det a) : ℂ) * φ g) * key

theorem fin_div {D : D7} {n : ℕ} {G' : Type} [Group G'] [TopologicalSpace G']
    (Ψ : GlobalTheory.StdUnn.G D n ≃ₜ* G') (K' : Subgroup G') (η : G' → ℝ)
    (hK : ∀ g, g ∈ GlobalTheory.StdUnn.K D n ↔ Ψ g ∈ K') (hright : ∀ g, ∀ k ∈ K', η (g * k) = η g)
    {φ : GlobalTheory.StdUnn.G D n → ℂ} (hφ : IsKFinite (GlobalTheory.StdUnn.K D n) φ) (t : ℂ) (f : GlobalTheory.StdUnn.G D n → ℂ)
    (hf : ∀ x, f x = φ x * Complex.exp (t * η (Ψ x))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K' => fun x => f (x * Ψ.symm k))) := by
  haveI : FiniteDimensional ℂ (kSpan (GlobalTheory.StdUnn.K D n) φ) := hφ
  refine Submodule.finiteDimensional_of_le (Submodule.span_le.2 ?_ :
    _ ≤ (kSpan (GlobalTheory.StdUnn.K D n) φ).map (LinearMap.mulRight ℂ (fun x => Complex.exp (t * η (Ψ x)))))
  rintro _ ⟨k, rfl⟩
  refine ⟨fun x => φ (x * Ψ.symm k), Submodule.subset_span ⟨Ψ.symm k, (hK _).2 (by simpa using k.2), rfl⟩, ?_⟩
  funext x
  simp [hf, LinearMap.mulRight_apply, map_mul, hright _ _ k.2]

theorem fun_eq {X : Type} (η : X → ℝ) (H : X → ℝ≥0) (hexp : ∀ x, Real.exp (η x) = (H x : ℝ)) (φ : X → ℂ)
    (s₁ z c : ℂ) : (fun x => Complex.exp ((z + c) * η x) * (φ x * Complex.exp (-(s₁ + c) * η x))) =
      fun x => ((H x : ℝ) : ℂ) ^ (z - s₁) * φ x := by
  funext x
  have hpos : (0 : ℝ) < H x := by rw [← hexp x]; exact Real.exp_pos _
  have hlog : Real.log (H x) = η x := by rw [← hexp x, Real.log_exp]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le, hlog]
  have key : Complex.exp ((z + c) * η x) * Complex.exp (-(s₁ + c) * η x) = Complex.exp (η x * (z - s₁)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  linear_combination φ x * key

theorem assemble {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [T2Space G'] [LocallyCompactSpace G'] (hFar : Far) (hGlue : Glue) (Φ : G ≃ₜ* G')
    (Γ P : Subgroup G) (Γ' K' P' : Subgroup G') (c : G' → ℂ) (η : G' → ℝ) (R0 : ℝ) (hK : IsCompact (K' : Set G'))
    (hPar : IsPar Γ' K' P' c) (hHt : IsHt Γ' K' P' η) (hΓ : ∀ g, g ∈ Γ ↔ Φ g ∈ Γ') (hP : ∀ g, g ∈ P ↔ Φ g ∈ P')
    (hconv : ∀ x : ℝ, R0 < x → Conv Γ' P' fun g => x * η g) (f : G → ℂ) (hf : Continuous f)
    (hlaw : ∀ q ∈ P, ∀ g, f (q * g) = c (Φ q) * f g) (A : ℂ → ℂ) (Hh : ℂ → G → ℂ) (R1 : ℝ) (hA : Differentiable ℂ A)
    (hAne : ∃ z, A z ≠ 0) (hHd : ∀ g, Differentiable ℂ (Hh · g)) (hHc : Continuous fun y : ℂ × G => Hh y.1 y.2)
    (hHeq : ∀ z : ℂ, R1 < z.re → ∀ g, Hh z g = A z * GlobalTheory.Eis.cosetSum P Γ (fun x => Complex.exp (z * η (Φ x)) * f x) g)
    (w : ℝ) (F : ℂ → G → ℂ) (hF : ∀ z : ℂ, (fun x => Complex.exp ((z + (w : ℂ)) * η (Φ x)) * f x) = F z) (s₀ : ℂ) :
    ∃ (U : Set ℂ) (d : Polynomial ℂ) (E : ℂ → G → ℂ) (σ : ℝ), IsOpen U ∧ IsRightDomain U ∧ s₀ ∈ U ∧ d ≠ 0 ∧
      (∀ g, DifferentiableOn ℂ (E · g) U) ∧ ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ Set.univ) ∧
      (∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g) ∧
      ∀ z : ℂ, σ < z.re → (∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets P Γ → ℝ, Summable u ∧
          ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term P Γ (F z) g q‖ ≤ u q) ∧
        ∀ g, E z g = d.eval z * GlobalTheory.Eis.cosetSum P Γ (F z) g := by
  obtain ⟨R, hR1, hR0⟩ : ∃ R : ℝ, R1 ≤ R ∧ R0 ≤ R := ⟨max R1 R0, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨hmaj, hdiff, hcont, hinv⟩ := hFar G G' Φ Γ P Γ' K' P' c η R hK hPar hHt hΓ hP
    (fun x hx => hconv x (lt_of_le_of_lt hR0 hx)) f hf hlaw
  obtain ⟨U', d', E', hU'o, hU'r, hs₀', hd', hE'd, hE'c, hE'i, hE'eq⟩ :=
    hGlue G Γ (fun i x => (i : G) * x)
      (fun z g => GlobalTheory.Eis.cosetSum P Γ (fun x => Complex.exp (z * η (Φ x)) * f x) g) Hh A R hA hAne hHd hHc
      (fun z hz x => hHeq z (lt_of_le_of_lt hR1 hz) x) hdiff hcont
      (fun z i x => hinv z i i.2 x) (s₀ + (w : ℂ))
  refine ⟨(· + (w : ℂ)) ⁻¹' U', Polynomial.taylor (w : ℂ) d', fun z g => E' (z + (w : ℂ)) g,
    R - w, hU'o.preimage (continuous_id.add continuous_const), hU'r.preimage_add _, hs₀', ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hd' ((Polynomial.taylor_eq_zero _ d').1 h)
  · intro g
    exact (hE'd g).comp (differentiableOn_id.add_const _) (fun z hz => hz)
  · refine hE'c.comp ((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn ?_
    intro y hy
    exact ⟨hy.1, Set.mem_univ _⟩
  · intro z hz γ hγ g
    exact hE'i (z + (w : ℂ)) hz ⟨γ, hγ⟩ g
  · intro z hz
    have hz' : R < (z + (w : ℂ)).re := by
      have : (z + (w : ℂ)).re = z.re + w := by simp
      rw [this]; linarith
    refine ⟨fun C hC => ?_, fun g => ?_⟩
    · obtain ⟨u, hu, hb⟩ := hmaj (z + (w : ℂ)) hz' C hC
      refine ⟨u, hu, fun g hg q => ?_⟩
      rw [← hF z]
      exact hb g hg q
    · show E' (z + (w : ℂ)) g = _
      rw [hE'eq (z + (w : ℂ)) hz' g, Polynomial.taylor_eval, hF z]

theorem eTop : ETop := by
  intro hDict hDI hCM hGT hBd hExt hPar hSg hStd hIwa hScal hFar hGlue
  intro D n hn χ b hχ hres H hH s₁ φ hφ s₀
  have hcm := GlobalTheory.AdelicU.isCMExt_host D
  have hur := GlobalTheory.HeckeAdjoint.unramified_host D
  have hpow := GlobalTheory.LFun.resEtaPow_of_resEta _ _ hcm.2.2.1 χ b ((GlobalTheory.LFun.resEta_iff χ b).1 hres)
  have hGood : (adCM D.sp.cm.sig χ).Good := hCM _ _ D.sp.cm.sig χ b hcm hur hχ hpow
  obtain ⟨_, _, _, hT2, hLC, _, hKc⟩ := hGT _ _ (adCM D.sp.cm.sig χ) hGood (Fin n) (-1)
  obtain ⟨Ψ, hΓ, hP, hK, hdet⟩ := hStd hDict hDI D χ n
  have hI := hIwa D χ n
  obtain ⟨hPar1, hHt1, -⟩ := (hPar _ _ (adCM D.sp.cm.sig χ) hGood (Fin n) (-1) Set.univ).2 (by rw [inf_idem]; exact hI)
  rw [inf_idem] at hPar1
  have hW := hSg _ _ D.sp.cm.sig χ b hcm hur hχ hpow (-1) (Fin n) (by simp; omega) hI
  have hexp : ∀ x, Real.exp ((adCM D.sp.cm.sig χ).uH (-1) Set.univ (Ψ x)) = (H x : ℝ) :=
    fun x => exp_uH_eq hDict hBd hGood Ψ hP hK hdet hI hH x
  obtain ⟨R0, D0, Op0, H0, hwall⟩ := hW ℂ (1 : (adCM D.sp.cm.sig χ).uK (-1) (Fin n) →* (ℂ →L[ℂ] ℂ)) continuous_const
  have hf : Continuous fun x => φ x * Complex.exp (-(s₁ + (n : ℂ) / 2) * (adCM D.sp.cm.sig χ).uH (-1) Set.univ (Ψ x)) :=
    hφ.2.1.mul (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (hHt1.cont.comp Ψ.continuous))))
  have hlaw := law_div Ψ _ _ ((adCM D.sp.cm.sig χ).uC (-1) (Fin n)) hP hHt1.left (fun g a ha => congrArg (fun u => ((χ u : Circle) : ℂ)) (hdet g a ha))
    hH hexp hφ
  have hfin := fin_div Ψ _ _ hK hHt1.right hφ.2.2 (-(s₁ + (n : ℂ) / 2))
    (fun x => φ x * Complex.exp (-(s₁ + (n : ℂ) / 2) * (adCM D.sp.cm.sig χ).uH (-1) Set.univ (Ψ x))) (fun x => rfl)
  obtain ⟨A0, Hh, R1, hA0, hA0ne, hHd, hHc, hHeq, -⟩ :=
    hScal _ _ Ψ _ _ _ _ _ _ _ _ hKc hPar1 hHt1 hΓ hP hW _ hf hlaw hfin
  exact assemble hFar hGlue Ψ _ _ _ _ _ _ _ R0 hKc hPar1 hHt1 hΓ hP hwall.convR _ hf hlaw A0 Hh R1 hA0 hA0ne hHd hHc hHeq
    ((n : ℝ) / 2) (fun z x => ((H x : ℝ) : ℂ) ^ (z - s₁) * φ x)
    (fun z => by
      have e := fun_eq (fun x => (adCM D.sp.cm.sig χ).uH (-1) Set.univ (Ψ x)) H hexp φ s₁ z ((n : ℂ) / 2)
      push_cast
      exact e) s₀

end GlobalTheory.CompanionTheory.SwEisTop
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOnUnitaryOfVanishAtOne
section
noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.Sep

variable {n : ℕ}

theorem sum_swap (X P Q : Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, X a b * (P a b - Q b a) = ∑ a, ∑ b, (X a b * P a b - X b a * Q a b) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

theorem real_linear_skew (L : Mat n →ₗ[ℝ] ℂ) (X : Mat n) (hX : Xᴴ = -X) :
    L X = ∑ a, ∑ b, X a b * ((1 / 2 : ℂ) * (L (Matrix.single a b 1) - Complex.I * L (Matrix.single a b Complex.I))
      - (1 / 2 : ℂ) * (L (Matrix.single b a 1) + Complex.I * L (Matrix.single b a Complex.I))) := by
  have hs : ∀ (a b : Fin n) (z : ℂ), Matrix.single a b z =
      z.re • Matrix.single a b (1 : ℂ) + z.im • Matrix.single a b Complex.I := by
    intro a b z
    ext i j
    by_cases h : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h
      simp [Complex.ext_iff]
    · have : ∀ w : ℂ, Matrix.single a b w i j = 0 := fun w => by
        rw [Matrix.single_apply_of_ne]
        tauto
      simp [this]
  have hX' : ∀ a b, X b a = -conj (X a b) := by
    intro a b
    have := congrFun (congrFun hX a) b
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at this
    have h2 := congrArg (starRingEnd ℂ) this
    simpa using h2
  have h1 : L X = ∑ a, ∑ b, (((X a b).re : ℂ) * L (Matrix.single a b 1) + ((X a b).im : ℂ) * L (Matrix.single a b Complex.I)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hs a b (X a b), map_add, map_smul, map_smul]
    simp [Complex.real_smul]
  rw [h1]
  refine Eq.trans ?_ (sum_swap (fun a b => X a b)
    (fun a b => (1 / 2 : ℂ) * (L (Matrix.single a b 1) - Complex.I * L (Matrix.single a b Complex.I)))
    (fun a b => (1 / 2 : ℂ) * (L (Matrix.single a b 1) + Complex.I * L (Matrix.single a b Complex.I)))).symm
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  beta_reduce
  rw [hX' a b]
  have hc : conj (X a b) = ((X a b).re : ℂ) - ((X a b).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hz : ((X a b).re : ℂ) + ((X a b).im : ℂ) * Complex.I = X a b := Complex.re_add_im _
  have key : ∀ x y p q : ℂ, x * p + y * q = (x + y * Complex.I) * ((1 / 2 : ℂ) * (p - Complex.I * q))
      - (-(x - y * Complex.I)) * ((1 / 2 : ℂ) * (p + Complex.I * q)) := by
    intro x y p q
    linear_combination (y * q) * Complex.I_sq
  have := key (X a b).re (X a b).im (L (Matrix.single a b 1)) (L (Matrix.single a b Complex.I))
  rw [hz, ← hc] at this
  exact this

theorem Kf_apply (a b : Fin n) (h : GlobalTheory.CompanionTheory.ModelS.SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    (GlobalTheory.CompanionTheory.ModelS.Kf a b h).1 g = (1 / 2 : ℂ) * (Rd (Matrix.single a b 1) h.1 g - Complex.I * Rd (Matrix.single a b Complex.I) h.1 g)
      - (1 / 2 : ℂ) * (Rd (Matrix.single b a 1) h.1 g + Complex.I * Rd (Matrix.single b a Complex.I) h.1 g) := by
  have e : (GlobalTheory.CompanionTheory.ModelS.Kf a b h).1 g = (e1 GlobalTheory.CompanionTheory.ModelS.DR a b h).1 g - (f1 GlobalTheory.CompanionTheory.ModelS.DR b a h).1 g := by
    simp [GlobalTheory.CompanionTheory.ModelS.Kf, e2, sub_eq_add_neg]
  rw [e, GlobalTheory.CompanionTheory.ModelS.orderedCechToCatCochainsOne_apply_valueAtSubset a b h hg, GlobalTheory.CompanionTheory.ModelS.liftOneFormsToCompatible_apply b a h hg]
  simp [Eu]
  ring

def AX (X : Mat n) : Module.End ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n) := ∑ a, ∑ b, X a b • GlobalTheory.CompanionTheory.ModelS.Kf a b

theorem AX_apply (X : Mat n) (hX : Xᴴ = -X) (w : GlobalTheory.CompanionTheory.ModelS.SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    (AX X w).1 g = Rd X w.1 g := by
  let L : Mat n →ₗ[ℝ] ℂ := ((fderiv ℝ w.1 g).comp (GlobalTheory.CompanionTheory.RCalc.mulL g)).toLinearMap
  have hL : ∀ v, L v = Rd v w.1 g := fun _ => rfl
  have e : (AX X w).1 g = ∑ a, ∑ b, X a b * (GlobalTheory.CompanionTheory.ModelS.Kf a b w).1 g := by
    simp [AX, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  rw [e, ← hL X, real_linear_skew L X hX]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Kf_apply a b w hg]
  rfl

theorem AX_mem (X : Mat n) (S : Submodule ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n))
    (hS : ∀ a b : Fin n, ∀ w ∈ S, GlobalTheory.CompanionTheory.ModelS.Kf a b w ∈ S) {w : GlobalTheory.CompanionTheory.ModelS.SmF n} (hw : w ∈ S) :
    AX X w ∈ S := by
  simp only [AX, LinearMap.sum_apply, LinearMap.smul_apply]
  exact S.sum_mem fun a _ => S.sum_mem fun b _ => S.smul_mem _ (hS a b w hw)

open scoped Matrix.Norms.Operator in
theorem exp_entry (X : Mat n) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) ((NormedSpace.exp ((t : ℂ) • X) * X) i j) t := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X t
  let L : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  have := L.hasFDerivAt.comp_hasDerivAt t h
  simp only [Complex.coe_smul] at this ⊢
  exact this

theorem exp_deriv (X : Mat n) (t : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) (NormedSpace.exp ((t : ℂ) • X) * X) t := by
  have : HasDerivAt (fun t : ℝ => (fun i j => (NormedSpace.exp ((t : ℂ) • X)) i j : Fin n → Fin n → ℂ))
      (fun i j => (NormedSpace.exp ((t : ℂ) • X) * X) i j) t := by
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro j
    exact exp_entry X t i j
  exact this

theorem exp_mem (X : Mat n) (t : ℝ) : NormedSpace.exp ((t : ℂ) • X) ∈ GLs n := by
  have h : IsUnit (NormedSpace.exp ((t : ℂ) • X)) := (GlobalTheory.CompanionTheory.GLK.expG X t).isUnit
  exact ((Matrix.isUnit_iff_isUnit_det _).1 h).ne_zero

theorem curve_deriv (X : Mat n) (hX : Xᴴ = -X) (w : GlobalTheory.CompanionTheory.ModelS.SmF n) (t : ℝ) :
    HasDerivAt (fun t : ℝ => w.1 (NormedSpace.exp ((t : ℂ) • X))) ((AX X w).1 (NormedSpace.exp ((t : ℂ) • X))) t := by
  have hg := exp_mem X t
  have hd := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth w.2.1 hg).hasFDerivAt
  have := hd.comp_hasDerivAt t (exp_deriv X t)
  rw [AX_apply X hX w hg]
  exact this

theorem ode_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (B : E →L[ℝ] E) (f : ℝ → E)
    (h : ∀ t, HasDerivAt f (B (f t)) t) (h0 : f 0 = 0) (t : ℝ) : f t = 0 := by
  have := ODE_solution_unique_univ (v := fun _ => B) (s := fun _ => Set.univ) (K := ‖B‖₊) (t₀ := 0)
    (f := f) (g := fun _ => 0)
    (fun _ => B.lipschitz.lipschitzOnWith)
    (fun t => ⟨h t, trivial⟩) (fun t => ⟨by simpa using hasDerivAt_const t (0 : E), trivial⟩) h0
  exact congrFun this t

theorem vanish_curve (S : Submodule ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n)) (fd : FiniteDimensional ℂ S)
    (hS : ∀ a b : Fin n, ∀ w ∈ S, GlobalTheory.CompanionTheory.ModelS.Kf a b w ∈ S) (h1 : ∀ w ∈ S, w.1 1 = 0)
    (X : Mat n) (hX : Xᴴ = -X) (t : ℝ) (w : GlobalTheory.CompanionTheory.ModelS.SmF n) (hw : w ∈ S) :
    w.1 (NormedSpace.exp ((t : ℂ) • X)) = 0 := by
  classical
  let bs := Module.finBasis ℂ S
  let C : Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ :=
    fun i j => bs.repr ⟨AX X (bs i).1, AX_mem X S hS (bs i).2⟩ j
  have hexp : ∀ (u : S) (g : Mat n), u.1.1 g = ∑ j, bs.repr u j * (bs j).1.1 g := by
    intro u g
    have h := congrArg (fun v : S => v.1.1 g) (bs.sum_repr u)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm
  let f : ℝ → Fin (Module.finrank ℂ S) → ℂ := fun t i => (bs i).1.1 (NormedSpace.exp ((t : ℂ) • X))
  let B : (Fin (Module.finrank ℂ S) → ℂ) →L[ℝ] (Fin (Module.finrank ℂ S) → ℂ) :=
    (LinearMap.toContinuousLinearMap (Matrix.toLin' C)).restrictScalars ℝ
  have hd : ∀ t, HasDerivAt f (B (f t)) t := by
    intro t
    rw [hasDerivAt_pi]
    intro i
    have hc := curve_deriv X hX (bs i).1 t
    have e : (AX X (bs i).1).1 (NormedSpace.exp ((t : ℂ) • X)) = B (f t) i := by
      have := hexp ⟨AX X (bs i).1, AX_mem X S hS (bs i).2⟩ (NormedSpace.exp ((t : ℂ) • X))
      refine this.trans ?_
      show _ = (C.mulVec (f t)) i
      rfl
    rw [← e]
    exact hc
  have h0 : f 0 = 0 := by
    funext i
    simpa [f] using h1 _ (bs i).2
  have hz := ode_zero B f hd h0 t
  rw [hexp ⟨w, hw⟩]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : (bs j).1.1 (NormedSpace.exp ((t : ℂ) • X)) = 0 := congrFun hz j
  rw [this, mul_zero]

theorem main : ∀ (n : ℕ) (S : Submodule ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n)), FiniteDimensional ℂ S →
    (∀ a b : Fin n, ∀ w ∈ S, GlobalTheory.CompanionTheory.ModelS.Kf a b w ∈ S) → (∀ w ∈ S, w.1 1 = 0) →
    ∀ w ∈ S, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, w.1 k.1 = 0 := by
  intro n S fd hS h1 w hw k
  obtain ⟨X, hX, hk⟩ := GlobalTheory.CompanionTheory.UnitaryLog.main n k
  have := vanish_curve S fd hS h1 X hX 1 w hw
  simp only [Complex.ofReal_one, one_smul] at this
  rw [hk]
  exact this

end GlobalTheory.CompanionTheory.ModelS.Sep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHaarUnitaryGroup
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem exists_rightInvariant_measure_unitaryGroup
    (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]
    [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] :
    ∃ κ : Measure (Matrix.unitaryGroup (Fin n) ℂ),
      IsFiniteMeasure κ ∧ κ.IsMulRightInvariant ∧ κ.IsOpenPosMeasure := by
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) :=
    GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  let μ : Measure (Matrix.unitaryGroup (Fin n) ℂ) := Measure.haarMeasure ⊤
  refine ⟨μ.inv, inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.CompanionTheory.ModelS
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightHermitianDerivationStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_highest_weight_hermitian_derivation : ∀ {n : ℕ} (ν : Fin n → ℤ), Antitone ν → ∃ (L : Type) (_ : NormedAddCommGroup L) (_ : InnerProductSpace ℂ L) (_ : FiniteDimensional ℂ L) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (L →ₗ[ℂ] L)) (K : Fin n → Fin n → Module.End ℂ L) (v : L), Formalism.REAL.GlRel K ∧ (∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ) ∧ IsDerivK σ K ∧ v ≠ 0 ∧ Formalism.REAL.KHighest (fun _ => true) K (wtR ν) v ∧ (∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v) ∧ ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z → LinearMap.trace ℂ L (σ k) = weylChar ν z := by
  first | exact @GlobalTheory.CompanionTheory.RmModel.rmModel | exact GlobalTheory.CompanionTheory.RmModel.rmModel | (intros; apply GlobalTheory.CompanionTheory.RmModel.rmModel <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSegmentRepresentation
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegExists

theorem hasFiniteLength_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL k)
    (hd : ∑ a, (x a).1 = N) : HasFiniteLength (prodIrr x hd) :=
  GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ (isSmooth_piTensor fun a => (x a).2.rep.smooth)
    (hasFiniteLength_of_isIrreducible (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA x))

theorem exists_isLSeg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k), ∃ π : IrrRep (GL (Fin Δ.deg) k), IsLSeg Δ π.ρ := by
  intro k _ _ _ _ hA Δ
  have hd : ∑ a, (Δ.term a).1 = Δ.deg := Δ.sum_term_fst
  obtain ⟨hd', ⟨φ⟩⟩ := GlobalTheory.T.contragredient_segment_product_equiv hA Δ hd
  obtain ⟨τ', hτ'⟩ := GlobalTheory.T.exists_socle_segment_product hA (segDual Δ) hd'
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra hA (prodIrr Δ.term hd)
    (isSmooth_prodIrr _ _) (hasFiniteLength_prodIrr hA _ _) τ' (hτ'.of_equiv (.refl _) φ.symm)
  exact ⟨τ, hd, hτ⟩

end GlobalTheory.CompanionTheory.SegExists

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantCommuteGenerator
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem epow_eq_pow_of {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    epow E m a b = ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [epow, Matrix.one_apply]
  | succ m ih => simp only [epow, pow_succ', Matrix.mul_apply, Matrix.of_apply, ih]

theorem gelA_central : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel E →
    ∀ (m : ℕ) (a b : Fin n), gelA E m * E a b = E a b * gelA E m := by
  intro n V _ _ E hE m a b
  rw [eq_comm, ← sub_eq_zero]
  simp only [gelA, epow_eq_pow_of]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [GlobalTheory.SmoothForms.comm_pow_of_apply E hE, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]

end GlobalTheory.CompanionTheory.ModelS
end

