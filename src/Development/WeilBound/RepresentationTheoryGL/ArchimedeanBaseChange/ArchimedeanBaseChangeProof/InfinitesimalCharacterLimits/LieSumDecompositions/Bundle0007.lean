import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle0005
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpFin
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0253
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1379
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetDiagonalBlockActsByInfinitesimalCharac
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0672
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0424
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0014

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksExp
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.PExpFin

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockExponential

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

def tl (r : ℕ) (s : ℝ) : Module.End ℂ (GA E N → ℂ) where
  toFun f g := f (aT E N r s * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tl_pow (r : ℕ) (s : ℝ) (i : ℕ) (f : GA E N → ℂ) : (tl r s ^ i) f = fun g => f (aT E N r (s * i) * g) := by
  induction i generalizing f with
  | zero =>
    funext g
    simp [aT_zero]
  | succ i ih =>
    funext g
    rw [pow_succ, Module.End.mul_apply, ih]
    show f (aT E N r s * (aT E N r (s * i) * g)) = f (aT E N r (s * ((i + 1 : ℕ) : ℝ)) * g)
    rw [← mul_assoc, ← aT_add, show s + s * (i : ℝ) = s * ((i + 1 : ℕ) : ℝ) by push_cast; ring]

theorem kl_iff (r : ℕ) (s : ℝ) (p : ℂ[X]) (F : GA E N → ℂ) : Kl r s p F ↔ aeval (tl r s) p F = 0 := by
  have e : aeval (tl (N := N) r s) p F = fun g => ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * F (aT E N r (s * j) * g) := by
    rw [aeval_eq_sum_range, LinearMap.sum_apply]
    funext g
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.smul_apply, tl_pow]
    rfl
  rw [e]
  constructor
  · intro h
    funext g
    exact h g
  · intro h g
    exact congrFun h g

theorem kl_mul {r : ℕ} {s : ℝ} {p q : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s p F) : Kl r s (p * q) F := by
  rw [kl_iff] at h ⊢
  rw [mul_comm, aeval_mul, Module.End.mul_apply, h, map_zero]

theorem kl_mul' {r : ℕ} {s : ℝ} {p q : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s q F) : Kl r s (p * q) F := by
  rw [mul_comm]
  exact kl_mul h

theorem ctn_eq_ct (r : ℕ) :
    letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
    ∃ μ : Measure (BlockIx N r → Ad E), μ.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratN E N r) (GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r) μ ∧
      ∀ f : Sm E N, An.ctn r f.1 = PositivityTheory.Affgl.CT.ct μ (GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r) f.1 := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, hμ, hD, hint⟩ := JDict.exists_normed E N r
  refine ⟨μ, hμ, hD, fun f => funext fun g => ?_⟩
  show An.ctn r f.1 g = ∫ x in GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r, f.1 (unip x * g) ∂μ
  rw [hint]
  simp only [An.ctn, GroundTheory.Automorphic.AutomorphicForm.constantTerm, GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip]

theorem ctn_add (r : ℕ) {φ ψ : Sm E N} (hφ : IsAutForm φ) (hψ : IsAutForm ψ) :
    An.ctn r (φ + ψ).1 = An.ctn r φ.1 + An.ctn r ψ.1 := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, hμ, hD, e⟩ := ctn_eq_ct (E := E) (N := N) r
  have := hμ
  rw [e, e, e]
  exact ct_add μ _ hD hφ hψ

theorem ctn_smul (r : ℕ) (c : ℂ) (φ : Sm E N) : An.ctn r (c • φ).1 = c • An.ctn r φ.1 := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  obtain ⟨μ, -, -, e⟩ := ctn_eq_ct (E := E) (N := N) r
  rw [e, e]
  exact ct_smul μ _ c φ

def Good (β : ℕ → ℝ) (φ : Sm E N) : Prop :=
  IsAutForm φ ∧ ∀ r, 0 < r → r < N → ∃ p : ℂ[X], p.Monic ∧ Kl r 1 p (An.ctn r φ.1) ∧ ∀ z, p.IsRoot z → ‖z‖ ≤ Real.exp (β r)

theorem good_bound {β : ℕ → ℝ} {φ : Sm E N} (h : Good β φ) :
    ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re ≤ β r := by
  intro r hr hrN c hc
  obtain ⟨p, -, hk, hroot⟩ := h.2 r hr hrN
  obtain ⟨F₀, hCT, F, hFspan, hF0, hFe⟩ := hc
  obtain ⟨-, -, -, hD⟩ := dict_holds E N
  obtain ⟨c₁, -, e₁⟩ := (hD φ h.1 r hr hrN).2 F₀ hCT
  have hk₀ : Kl r 1 p F₀ := by
    have : F₀ = c₁ • An.ctn r φ.1 := by
      funext g
      rw [e₁]
      rfl
    rw [this]
    exact (klSub r 1 p).smul_mem c₁ hk
  have hroot' := kl_eigen (kl_span hk₀ hFspan) hF0 hFe
  have h1 := hroot (Complex.exp (c * ((1 : ℝ) : ℂ))) hroot'
  rw [Complex.norm_exp] at h1
  have h2 := Real.exp_le_exp.1 h1
  simpa using h2

theorem good_of (β : ℕ → ℝ) {φ : Sm E N} (hφ : IsAutForm φ)
    (hexp : ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re ≤ β r) : Good β φ := by
  refine ⟨hφ, fun r hr hrN => ?_⟩
  obtain ⟨hA, -, -, hCT⟩ := dict_holds E N
  have hct := (hCT φ hφ r hr hrN).1
  have hfin := finTr_holds E N φ hφ r hr hrN _ hct
  have hadd : ∀ s t, aT E N r (s + t) = aT E N r s * aT E N r t := fun s t => aT_add r s t
  have hcont : ∀ g, Continuous fun t => An.ctn r φ.1 (aT E N r t * g) := by
    intro g
    have e : (fun t => An.ctn r φ.1 (aT E N r t * g)) = fun t => An.ctn r φ.1 (An.aR E N r t * g) :=
      funext fun t => by rw [hA]
    rw [e]
    exact JSqIntGlue.continuous_ctn_comp (GlobalTheory.CompanionTheory.ContAutForm.continuous_of_isAutForm_totallyComplex E N φ hφ) r
      ((JSqIntGlue.continuous_aR r).mul continuous_const)
  obtain ⟨p, hp, hpk, hroots⟩ := killPoly_holds (GA E N) (aT E N r) (An.ctn r φ.1) hadd hcont hfin
  refine ⟨p, hp, fun g => ?_, fun z hz => ?_⟩
  · have := hpk g
    simpa only [one_mul] using this
  · obtain ⟨c, rfl, F, hF, hF0, hFe⟩ := hroots z hz
    have hc : c ∈ Exp r φ.1 := ⟨_, hct, F, hF, hF0, hFe⟩
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (hexp r hr hrN c hc)

theorem good_add {β : ℕ → ℝ} {φ ψ : Sm E N} (hφ : Good β φ) (hψ : Good β ψ) : Good β (φ + ψ) := by
  refine ⟨GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_add hφ.1 hψ.1, fun r hr hrN => ?_⟩
  obtain ⟨p, hp, hpk, hpr⟩ := hφ.2 r hr hrN
  obtain ⟨q, hq, hqk, hqr⟩ := hψ.2 r hr hrN
  refine ⟨p * q, hp.mul hq, ?_, fun z hz => ?_⟩
  · rw [ctn_add r hφ.1 hψ.1]
    exact (klSub r 1 (p * q)).add_mem (kl_mul hpk) (kl_mul' hqk)
  · rcases (Polynomial.root_mul.1 hz) with h | h
    · exact hpr z h
    · exact hqr z h

theorem good_smul {β : ℕ → ℝ} {φ : Sm E N} (hφ : Good β φ) (c : ℂ) : Good β (c • φ) := by
  refine ⟨GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_smul c hφ.1, fun r hr hrN => ?_⟩
  obtain ⟨p, hp, hpk, hpr⟩ := hφ.2 r hr hrN
  refine ⟨p, hp, ?_, hpr⟩
  rw [ctn_smul]
  exact (klSub r 1 p).smul_mem c hpk

theorem good_zero (β : ℕ → ℝ) : Good β (0 : Sm E N) := by
  refine ⟨GlobalTheory.HCF.FormsSub.isAutForm_zero, fun r hr hrN => ⟨1, monic_one, ?_, fun z hz => ?_⟩⟩
  · have e : An.ctn r (0 : Sm E N).1 = (0 : ℂ) • An.ctn r (0 : Sm E N).1 := by
      rw [← ctn_smul, zero_smul]
    rw [e]
    exact (klSub r 1 1).smul_mem 0 (by
      intro g
      simp [An.ctn, GroundTheory.Automorphic.AutomorphicForm.constantTerm])
  · exact absurd hz (by simp [Polynomial.IsRoot])

theorem exp_span (S : Set (Sm E N)) (β : ℕ → ℝ) (haut : ∀ φ ∈ S, IsAutForm φ)
    (hexp : ∀ φ ∈ S, ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re ≤ β r) :
    ∀ φ ∈ Submodule.span ℂ S, ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re ≤ β r := by
  intro φ hφ
  refine good_bound ?_
  induction hφ using Submodule.span_induction with
  | mem x hx => exact good_of β (haut x hx) (hexp x hx)
  | zero => exact good_zero β
  | add x y _ _ hx hy => exact good_add hx hy
  | smul c x _ hx => exact good_smul hx c

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockExponential

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgA
section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

theorem h2 (r s : ℕ) : ∑ i, (![r, s] : Fin 2 → ℕ) i = r + s := CapFactor.two_sum _

def sl0 (m₂ : GA E s) : Sm E (r + s) →ₗ[ℂ] Sm E r :=
  GlobalTheory.BlockCap.restrLin (stdBlocks ![r, s] (h2 r s)) (CapFactor.levPair (1, m₂)) 0

def sl1 (m₁ : GA E r) : Sm E (r + s) →ₗ[ℂ] Sm E s :=
  GlobalTheory.BlockCap.restrLin (stdBlocks ![r, s] (h2 r s)) (CapFactor.levPair (m₁, 1)) 1

theorem update0 (m₁ : GA E r) (m₂ : GA E s) :
    Function.update (CapFactor.levPair (n := ![r, s]) (1, m₂)) 0 m₁ = CapFactor.levPair (m₁, m₂) := by
  funext i
  fin_cases i <;> rfl

theorem update1 (m₁ : GA E r) (m₂ : GA E s) :
    Function.update (CapFactor.levPair (n := ![r, s]) (m₁, 1)) 1 m₂ = CapFactor.levPair (m₁, m₂) := by
  funext i
  fin_cases i <;> rfl

theorem left_slice_apply (m₂ : GA E s) (F : Sm E (r + s)) (m₁ : GA E r) :
    (sl0 m₂ F).1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂)) := by
  show F.1 (leviEmb (Ad E) (stdBlocks ![r, s] (h2 r s))
    (Function.update (CapFactor.levPair (n := ![r, s]) (1, m₂)) 0 m₁)) = _
  rw [update0]
  exact congrArg F.1 (CapFactor.lev_eq_leviEmb (R := Ad E) ![r, s] (h2 r s) (m₁, m₂)).symm

theorem right_slice_apply (m₁ : GA E r) (F : Sm E (r + s)) (m₂ : GA E s) :
    (sl1 m₁ F).1 m₂ = F.1 (lev (Ad E) r s (m₁, m₂)) := by
  show F.1 (leviEmb (Ad E) (stdBlocks ![r, s] (h2 r s))
    (Function.update (CapFactor.levPair (n := ![r, s]) (m₁, 1)) 1 m₂)) = _
  rw [update1]
  exact congrArg F.1 (CapFactor.lev_eq_leviEmb (R := Ad E) ![r, s] (h2 r s) (m₁, m₂)).symm

example {a : ℕ} (A B : Matrix (Fin a) (Fin a) (Cinf E)) : toL (A + B) = toL A + toL B := rfl

theorem yp_one {a : ℕ} : BlockDerivatives.yp (1 : Kinf E a) (1 : GL (Fin a) (Af E)) = 1 := by
  simp [BlockDerivatives.yp]

abbrev e2 (r s : ℕ) := stdBlocks ![r, s] (h2 r s)

theorem left_slice_lie_first_block (m₂ : GA E s) (Y : Lie E r) (F : Sm E (r + s)) :
    sl0 m₂ (lie E (r + s) (GlobalTheory.BlockCap.blockCLM (e2 r s) 0 Y) F) = lie E r Y (sl0 m₂ F) :=
  LinearMap.congr_fun (GlobalTheory.BlockCap.restrLin_lie (e2 r s) (CapFactor.levPair (1, m₂)) 0 Y) F

theorem right_slice_lie_second_block (m₁ : GA E r) (Y : Lie E s) (F : Sm E (r + s)) :
    sl1 m₁ (lie E (r + s) (GlobalTheory.BlockCap.blockCLM (e2 r s) 1 Y) F) = lie E s Y (sl1 m₁ F) :=
  LinearMap.congr_fun (GlobalTheory.BlockCap.restrLin_lie (e2 r s) (CapFactor.levPair (m₁, 1)) 1 Y) F

theorem std0 (p : Fin r) : (e2 r s) ⟨0, p⟩ = Fin.castAdd s p := CapFactor.std_zero ![r, s] (h2 r s) p

theorem std1 (q : Fin s) : (e2 r s) ⟨1, q⟩ = Fin.natAdd r q := CapFactor.std_one ![r, s] (h2 r s) q

theorem lev_eq (m : GA E r × GA E s) : lev (Ad E) r s m = leviEmb (Ad E) (e2 r s) (CapFactor.levPair m) :=
  CapFactor.lev_eq_leviEmb ![r, s] (h2 r s) m

theorem toL_single_cc (p q : Fin r) (x : Cinf E) :
    (toL (Matrix.single (Fin.castAdd s p) (Fin.castAdd s q) x) : Lie E (r + s)) =
      GlobalTheory.BlockCap.blockCLM (e2 r s) 0 (toL (Matrix.single p q x)) := by
  have h := GlobalTheory.BlockCap.blockLin_single (E := E) (e2 r s) 0 p q x
  rw [std0, std0] at h
  exact h.symm

theorem toL_single_nn (p q : Fin s) (x : Cinf E) :
    (toL (Matrix.single (Fin.natAdd r p) (Fin.natAdd r q) x) : Lie E (r + s)) =
      GlobalTheory.BlockCap.blockCLM (e2 r s) 1 (toL (Matrix.single p q x)) := by
  have h := GlobalTheory.BlockCap.blockLin_single (E := E) (e2 r s) 1 p q x
  rw [std1, std1] at h
  exact h.symm

theorem unipRad_inv (F : Sm E (r + s)) (hF : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g) :
    ∀ u ∈ unipRad (Ad E) (e2 r s), ∀ g, F.1 (u * g) = F.1 g := fun u hu g => by
  obtain ⟨x, rfl⟩ := CapFactor.exists_unip_of_mem ![r, s] (h2 r s) hu
  exact hF x g

theorem lie_upper_lev (F : Sm E (r + s)) (hF : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (p : Fin r) (q : Fin s) (x : Cinf E) (m : GA E r × GA E s) :
    (lie E (r + s) (toL (Matrix.single (Fin.castAdd s p) (Fin.natAdd r q) x)) F).1 (lev (Ad E) r s m) = 0 := by
  have hpq : blk (e2 r s) (Fin.castAdd s p) < blk (e2 r s) (Fin.natAdd r q) := by
    have b0 : blk (e2 r s) ((e2 r s) ⟨0, p⟩) = 0 := blk_apply (e2 r s) 0 p
    have b1 : blk (e2 r s) ((e2 r s) ⟨1, q⟩) = 1 := blk_apply (e2 r s) 1 q
    rw [std0] at b0
    rw [std1] at b1
    rw [b0, b1]
    decide
  have := GlobalTheory.UnipZero.lieD_single_leviEmb_eq_zero E ![r, s] (e2 r s) F (unipRad_inv F hF) _ _ hpq x
    (CapFactor.levPair m)
  rw [lev_eq]
  exact this

theorem lie_sum_single (X : Lie E (r + s)) (F : Sm E (r + s)) :
    lie E (r + s) X F = ∑ p, ∑ q, lie E (r + s) (toL (Matrix.single p q (X p q))) F := by
  have hdec : X = ∑ p, ∑ q, (toL (Matrix.single p q (X p q)) : Lie E (r + s)) :=
    Matrix.matrix_eq_sum_single (Matrix.of X)
  conv_lhs => rw [hdec]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_sum, LinearMap.sum_apply]

theorem right_slice_eq_sum (F : Sm E (r + s)) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2) (m₁ : GA E r) :
    sl1 m₁ F = ∑ i, (b i).1 m₁ • q i := by
  refine Subtype.ext (funext fun m₂ => ?_)
  rw [right_slice_apply, hexp (m₁, m₂), Submodule.coe_sum, Finset.sum_apply]
  rfl

theorem left_slice_eq_sum (F : Sm E (r + s)) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2) (m₂ : GA E s) :
    sl0 m₂ F = ∑ i, (q i).1 m₂ • b i := by
  refine Subtype.ext (funext fun m₁ => ?_)
  rw [left_slice_apply, hexp (m₁, m₂), Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  change _ = (q i).1 m₂ * (b i).1 m₁
  ring

theorem left_slice_lie_second_block (F : Sm E (r + s)) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2) (Y : Lie E s)
    (m₂ : GA E s) :
    sl0 m₂ (lie E (r + s) (GlobalTheory.BlockCap.blockCLM (e2 r s) 1 Y) F) = ∑ i, (lie E s Y (q i)).1 m₂ • b i := by
  refine Subtype.ext (funext fun m₁ => ?_)
  rw [left_slice_apply, ← right_slice_apply, right_slice_lie_second_block, right_slice_eq_sum F b q hexp, map_sum, Submodule.coe_sum, Finset.sum_apply,
    Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  change (b i).1 m₁ * (lie E s Y (q i)).1 m₂ = (lie E s Y (q i)).1 m₂ * (b i).1 m₁
  ring

theorem right_slice_lie_first_block (F : Sm E (r + s)) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2) (Y : Lie E r)
    (m₁ : GA E r) :
    sl1 m₁ (lie E (r + s) (GlobalTheory.BlockCap.blockCLM (e2 r s) 0 Y) F) = ∑ i, (lie E r Y (b i)).1 m₁ • q i := by
  refine Subtype.ext (funext fun m₂ => ?_)
  rw [right_slice_apply, ← left_slice_apply, left_slice_lie_first_block, left_slice_eq_sum F b q hexp, map_sum, Submodule.coe_sum, Finset.sum_apply,
    Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  change (q i).1 m₂ * (lie E r Y (b i)).1 m₁ = (lie E r Y (b i)).1 m₁ * (q i).1 m₂
  ring

theorem left_slice_single_first (m₂ : GA E s) (p q : Fin r) (x : Cinf E) (F : Sm E (r + s)) :
    sl0 m₂ (lie E (r + s) (toL (Matrix.single (Fin.castAdd s p) (Fin.castAdd s q) x)) F) =
      lie E r (toL (Matrix.single p q x)) (sl0 m₂ F) := by
  rw [toL_single_cc]
  exact left_slice_lie_first_block m₂ _ F

theorem right_slice_single_second (m₁ : GA E r) (p q : Fin s) (x : Cinf E) (F : Sm E (r + s)) :
    sl1 m₁ (lie E (r + s) (toL (Matrix.single (Fin.natAdd r p) (Fin.natAdd r q) x)) F) =
      lie E s (toL (Matrix.single p q x)) (sl1 m₁ F) := by
  rw [toL_single_nn]
  exact right_slice_lie_second_block m₁ _ F

theorem left_slice_single_second (F : Sm E (r + s)) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2) (p p' : Fin s)
    (x : Cinf E) (m₂ : GA E s) :
    sl0 m₂ (lie E (r + s) (toL (Matrix.single (Fin.natAdd r p) (Fin.natAdd r p') x)) F) =
      ∑ i, (lie E s (toL (Matrix.single p p' x)) (q i)).1 m₂ • b i := by
  rw [toL_single_nn]
  exact left_slice_lie_second_block F b q hexp _ m₂

theorem right_slice_single_first (F : Sm E (r + s)) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2) (p p' : Fin r)
    (x : Cinf E) (m₁ : GA E r) :
    sl1 m₁ (lie E (r + s) (toL (Matrix.single (Fin.castAdd s p) (Fin.castAdd s p') x)) F) =
      ∑ i, (lie E r (toL (Matrix.single p p' x)) (b i)).1 m₁ • q i := by
  rw [toL_single_cc]
  exact right_slice_lie_first_block F b q hexp _ m₁

theorem key_left (W : Submodule ℂ (Sm E r)) (hW : IsStable W) (F : Sm E (r + s))
    (hu : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (hP : ∀ m₂, sl0 m₂ F ∈ W) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s) (hb : ∀ i, b i ∈ W)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2)
    (X : Lie E (r + s)) (hX : ∀ (i : Fin s) (j : Fin r), X (Fin.natAdd r i) (Fin.castAdd s j) = 0)
    (m₂ : GA E s) : sl0 m₂ (lie E (r + s) X F) ∈ W := by
  rw [lie_sum_single, map_sum]
  refine W.sum_mem fun p _ => ?_
  rw [map_sum]
  refine W.sum_mem fun q' _ => ?_
  induction p using Fin.addCases with
  | left p =>
    induction q' using Fin.addCases with
    | left q' =>
      rw [left_slice_single_first]
      exact hW (.lie _) _ (hP m₂)
    | right q' =>
      have h0 : sl0 m₂ (lie E (r + s) (toL (Matrix.single (Fin.castAdd s p) (Fin.natAdd r q')
          (X (Fin.castAdd s p) (Fin.natAdd r q')))) F) = 0 :=
        Subtype.ext (funext fun m₁ => by rw [left_slice_apply]; exact lie_upper_lev F hu p q' _ (m₁, m₂))
      rw [h0]
      exact W.zero_mem
  | right p =>
    induction q' using Fin.addCases with
    | left q' =>
      rw [hX p q', Matrix.single_zero]
      have : (toL (0 : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) : Lie E (r + s)) = 0 := rfl
      rw [this, map_zero, LinearMap.zero_apply, map_zero]
      exact W.zero_mem
    | right q' =>
      rw [left_slice_single_second F b q hexp]
      exact W.sum_mem fun i _ => W.smul_mem _ (hb i)

theorem key_right (W : Submodule ℂ (Sm E s)) (hW : IsStable W) (F : Sm E (r + s))
    (hu : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (hP : ∀ m₁, sl1 m₁ F ∈ W) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s) (hq : ∀ i, q i ∈ W)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2)
    (X : Lie E (r + s)) (hX : ∀ (i : Fin s) (j : Fin r), X (Fin.natAdd r i) (Fin.castAdd s j) = 0)
    (m₁ : GA E r) : sl1 m₁ (lie E (r + s) X F) ∈ W := by
  rw [lie_sum_single, map_sum]
  refine W.sum_mem fun p _ => ?_
  rw [map_sum]
  refine W.sum_mem fun q' _ => ?_
  induction p using Fin.addCases with
  | left p =>
    induction q' using Fin.addCases with
    | left q' =>
      rw [right_slice_single_first F b q hexp]
      exact W.sum_mem fun i _ => W.smul_mem _ (hq i)
    | right q' =>
      have h0 : sl1 m₁ (lie E (r + s) (toL (Matrix.single (Fin.castAdd s p) (Fin.natAdd r q')
          (X (Fin.castAdd s p) (Fin.natAdd r q')))) F) = 0 :=
        Subtype.ext (funext fun m₂ => by rw [right_slice_apply]; exact lie_upper_lev F hu p q' _ (m₁, m₂))
      rw [h0]
      exact W.zero_mem
  | right p =>
    induction q' using Fin.addCases with
    | left q' =>
      rw [hX p q', Matrix.single_zero]
      have : (toL (0 : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) : Lie E (r + s)) = 0 := rfl
      rw [this, map_zero, LinearMap.zero_apply, map_zero]
      exact W.zero_mem
    | right q' =>
      rw [right_slice_single_second]
      exact hW (.lie _) _ (hP m₁)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
end
end

