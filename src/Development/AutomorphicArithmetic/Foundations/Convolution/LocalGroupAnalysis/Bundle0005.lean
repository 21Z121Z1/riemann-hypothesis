import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.MonicPolynomialIsMatrixCharpoly
section
open PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Loc Polynomial

private theorem exists_matrix_charpoly {k : Type} [Field k] (P : k[X]) (hP : P.Monic) (n : ℕ)
    (hn : P.natDegree = n) : ∃ M : Matrix (Fin n) (Fin n) k, M.charpoly = P := by
  subst hn
  have hP0 : P ≠ 0 := hP.ne_zero
  have hdim : (AdjoinRoot.powerBasis hP0).dim = P.natDegree := AdjoinRoot.powerBasis_dim hP0
  refine ⟨Matrix.reindex (finCongr hdim) (finCongr hdim)
    (Algebra.leftMulMatrix (AdjoinRoot.powerBasis hP0).basis (AdjoinRoot.powerBasis hP0).gen), ?_⟩
  rw [Matrix.charpoly_reindex, charpoly_leftMulMatrix, AdjoinRoot.minpoly_powerBasis_gen hP0]
  simp [hP.leadingCoeff]

theorem UpperTheory.ConvolutionTheory.G.monic_polynomial_is_matrix_charpoly :
    N1 := by
  intro k E _ _ _ _ _ _ σ hgen n δ hreg
  obtain ⟨P, hP⟩ := charpoly_normGL_lifts σ hgen δ
  have hPm : P.Monic := Polynomial.monic_of_injective (algebraMap k E).injective
    (by rw [hP]; exact Matrix.charpoly_monic _)
  have hdeg : P.natDegree = n := by
    rw [← Polynomial.natDegree_map (f := algebraMap k E), hP, Matrix.charpoly_natDegree_eq_dim]
    simp
  obtain ⟨M, hM⟩ := exists_matrix_charpoly P hPm n hdeg
  have hMc : (M.map (algebraMap k E)).charpoly = ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly := by
    rw [Matrix.charpoly_map, hM, hP]
  have hdetE : (M.map (algebraMap k E)).det = ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, Matrix.det_eq_sign_charpoly_coeff, hMc]
  have hNu : IsUnit ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (normGL σ δ).isUnit
  have hdet : IsUnit M.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [← hdetE] at hNu
    have e : (M.map (algebraMap k E)).det = algebraMap k E M.det := ((algebraMap k E).map_det M).symm
    rw [e, h0, map_zero] at hNu
    exact not_isUnit_zero hNu
  let γ : GL (Fin n) k := Matrix.nonsingInvUnit M hdet
  have hγ : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = M.map (algebraMap k E) := rfl
  obtain ⟨x, hx⟩ := (UpperTheory.ConvolutionTheory.D.conjSep E E n _ hreg).1 ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
    (by rw [hγ]; exact hMc)
  have hx' : normGL σ δ * x = x * incl γ := Units.ext hx
  refine ⟨x, γ, ?_⟩
  have hℓ : σ ^ Module.finrank k E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, hℓ, sigmaGL_one]
  have h := twNorm_twConj_of_pow_eq_one (sigmaGL σ) hθ x δ
  change twNorm (sigmaGL σ) (Module.finrank k E) (twConj (sigmaGL σ) x δ) = incl γ
  rw [h]
  change x⁻¹ * normGL σ δ * x = incl γ
  rw [mul_assoc, hx', inv_mul_cancel_left]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.OrbitalIntegralAbsoluteConvergence
section
open PositivityTheory.Rg.Tf.Geo
open MeasureTheory
open scoped ENNReal

private theorem finite_fiber_integral {X T : Type} [Group X] [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] [Group T]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (i : T →* X) (Φ : X → ℂ) (ρ : X → NNReal) (hΦ : Continuous Φ)
    (hρ : Continuous ρ) (hC : ∃ C, IsCompact C ∧ ∀ x, Φ x ≠ 0 → ∃ t, ∃ y ∈ C, x = i t * y)
    (h : ∀ C : Set X, IsCompact C → ∃ C' : Set X, IsCompact C' ∧ ∀ t, ∀ x ∈ C, ρ (i t * x) ≠ 0 → i t * x ∈ C') :
    ∫⁻ x, ‖Φ x‖ₑ * (ρ x : ℝ≥0∞) ∂μ < ⊤ := by
  obtain ⟨C, hC, hs⟩ := hC
  obtain ⟨C', hC', hs'⟩ := h C hC
  have hc : Continuous fun x => Φ x * ((ρ x : ℝ) : ℂ) :=
    hΦ.mul (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hρ))
  have hk : HasCompactSupport fun x => Φ x * ((ρ x : ℝ) : ℂ) := by
    refine HasCompactSupport.intro hC' fun x hx => ?_
    by_contra hne
    have h1 : Φ x ≠ 0 := left_ne_zero_of_mul hne
    have h2 : ρ x ≠ 0 := by
      intro h0
      exact hne (by simp [h0])
    obtain ⟨t, y, hy, rfl⟩ := hs x h1
    exact hx (hs' t y hy h2)
  have hi := (hc.integrable_of_hasCompactSupport (μ := μ) hk).2
  unfold HasFiniteIntegral at hi
  convert hi using 3 with x
  rw [enorm_mul]
  congr 1
  simp [enorm]

private theorem prod_isInvInvariant {T T' : Type} [Group T] [MeasurableSpace T] [MeasurableInv T] [Group T'] [MeasurableSpace T']
    [MeasurableInv T'] (ν : Measure T) (ν' : Measure T') [SFinite ν] [SFinite ν'] [ν.IsInvInvariant] [ν'.IsInvInvariant] :
    (ν.prod ν').IsInvInvariant := by
  constructor
  exact ((Measure.measurePreserving_inv ν).prod (Measure.measurePreserving_inv ν')).map_eq

theorem UpperTheory.ConvolutionTheory.G.orbitalIntegral_absolute_convergence :
    Q1 → Q2 → Q3 := by
  intro h1 h2 X T X' T' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ μ' _ ν' _ _ _ _ _
    i i' hi hi' Φ Φ' hΦ hΦ' hinv hinv' hC hC'
  obtain ⟨ρ, hρ, hn, hs⟩ := h2 X T ν i hi
  obtain ⟨ρ', hρ', hn', hs'⟩ := h2 X' T' ν' i' hi'
  have f1 := finite_fiber_integral μ i Φ ρ hΦ hρ hC hs
  have f2 := finite_fiber_integral μ' i' Φ' ρ' hΦ' hρ' hC' hs'
  have e1 := h1 X X T μ ν (MonoidHom.id X) i measurable_id hi.continuous Φ _ hΦ.measurable hinv hn f1
  have e2 := h1 X' X' T' μ' ν' (MonoidHom.id X') i' measurable_id hi'.continuous Φ' _ hΦ'.measurable hinv' hn' f2
  haveI := prod_isInvInvariant ν ν'
  have hn3 : IsNormAlong id (fun t : T × T' => (i t.1, i' t.2)) (ν.prod ν')
      (fun x : X × X' => (ρ x.1 : ℝ≥0∞) * (ρ' x.2 : ℝ≥0∞)) := by
    refine ⟨(hn.1.comp measurable_fst).mul (hn'.1.comp measurable_snd), fun x => ?_⟩
    have a1 : Measurable fun t => (ρ (i t * x.1) : ℝ≥0∞) :=
      hn.1.comp (hi.continuous.mul continuous_const).measurable
    have a2 : Measurable fun t => (ρ' (i' t * x.2) : ℝ≥0∞) :=
      hn'.1.comp (hi'.continuous.mul continuous_const).measurable
    have := lintegral_prod_mul (μ := ν) (ν := ν') a1.aemeasurable a2.aemeasurable
    have b1 := hn.2 x.1
    have b2 := hn'.2 x.2
    simp only [id] at b1 b2
    rw [b1, b2, mul_one] at this
    exact this
  have f3 : ∫⁻ x : X × X', ‖Φ x.1 * Φ' x.2‖ₑ * ((ρ x.1 : ℝ≥0∞) * (ρ' x.2 : ℝ≥0∞)) ∂(μ.prod μ') < ⊤ := by
    have a1 : Measurable fun x => ‖Φ x‖ₑ * (ρ x : ℝ≥0∞) := hΦ.measurable.enorm.mul hn.1
    have a2 : Measurable fun x => ‖Φ' x‖ₑ * (ρ' x : ℝ≥0∞) := hΦ'.measurable.enorm.mul hn'.1
    have := lintegral_prod_mul (μ := μ) (ν := μ') a1.aemeasurable a2.aemeasurable
    refine lt_of_eq_of_lt ?_ (this ▸ ENNReal.mul_lt_top f1 f2)
    refine lintegral_congr fun x => ?_
    rw [enorm_mul]
    ring
  have e3 := h1 (X × X') (X × X') (T × T') (μ.prod μ') (ν.prod ν') (MonoidHom.id _) (i.prodMap i') measurable_id
    (hi.continuous.prodMap hi'.continuous) (fun x => Φ x.1 * Φ' x.2) _
    ((hΦ.measurable.comp measurable_fst).mul (hΦ'.measurable.comp measurable_snd))
    (fun t x => by
      show Φ (i t.1 * x.1) * Φ' (i' t.2 * x.2) = _
      rw [hinv, hinv']) hn3 f3
  refine e3.trans (Eq.trans ?_ (congrArg₂ (· * ·) e1 e2).symm)
  rw [← integral_prod_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [MonoidHom.id_apply, ENNReal.toReal_mul, Complex.ofReal_mul]
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Topology Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G
open scoped ENNReal NumberField.AdeleRing

namespace UpperTheory.ConvolutionTheory.T4

section

abbrev Pl (K : Type) [Field K] : Type := HeightOneSpectrum (𝓞 K)

variable (K : Type) [Field K] [NumberField K] (n : ℕ)

abbrev GA : Type := AdelicGLn.AdelicGL K n

abbrev pI : GA K n →* GL (Fin n) (InfiniteAdeleRing K) := mapGL n (RingHom.fst _ _)

def pF (v : Pl K) : GA K n →* GL (Fin n) (v.adicCompletion K) where
  toFun := finAt v
  map_one' := Units.ext (by ext a b; simp only [finAt_apply, Units.val_one, Matrix.one_apply]; split_ifs <;> rfl)
  map_mul' := finAt_mul v

theorem pF_apply (v : Pl K) (g : GA K n) : pF K n v g = finAt v g := rfl

abbrev KF (v : Pl K) : Subgroup (GL (Fin n) (v.adicCompletion K)) := GLnLocal.integralGL (v.adicCompletion K) n

abbrev zA (s : ℝ) : GA K n := centralSection K n ⟨Real.exp s, Real.exp_pos s⟩

variable {K n}

abbrev TA (γ : GL (Fin n) K) : Subgroup (GA K n) := Subgroup.centralizer {AdelicGLn.diagonal K n γ}

abbrev TI (γ : GL (Fin n) K) : Subgroup (GL (Fin n) (InfiniteAdeleRing K)) :=
  Subgroup.centralizer {pI K n (AdelicGLn.diagonal K n γ)}

abbrev TF (γ : GL (Fin n) K) (v : Pl K) : Subgroup (GL (Fin n) (v.adicCompletion K)) :=
  Subgroup.centralizer {pF K n v (AdelicGLn.diagonal K n γ)}

abbrev EulT [MeasurableSpace (GL (Fin n) (InfiniteAdeleRing K))] [∀ v : Pl K, MeasurableSpace (GL (Fin n) (v.adicCompletion K))]
    (γ : GL (Fin n) K) (ν : Measure (TA γ)) (νi : Measure (TI γ)) (nv : ∀ v : Pl K, Measure (TF γ v)) (b : NNReal)
    (S : Finset (Pl K)) : Prop :=
  Eul (cen (pI K n) (AdelicGLn.diagonal K n γ)) (fun v => cen (pF K n v) (AdelicGLn.diagonal K n γ))
    (fun v => (KF K n v).comap (TF γ v).subtype) ν νi nv b S

def FF (γ : GL (Fin n) K) (Φ : GA K n → ℂ) (x : GA K n) : ℂ :=
  ∫ s : ℝ, Φ (zA K n s * (x⁻¹ * AdelicGLn.diagonal K n γ * x))

end

section

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E] (n : ℕ)

variable (F) in

abbrev infMap : InfiniteAdeleRing F →+* InfiniteAdeleRing E :=
  GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)

abbrev pE (v : Pl F) : GA E n →* GL (Fin n) (CompletionsOver E v) := mapGL n (atFin v)

def KE (v : Pl F) : Subgroup (GL (Fin n) (CompletionsOver E v)) where
  carrier := unitSet E n v
  one_mem' w := by rw [map_one]; exact one_mem _
  mul_mem' {a b} ha hb w := by rw [map_mul]; exact mul_mem (ha w) (hb w)
  inv_mem' {a} ha w := by rw [map_inv]; exact inv_mem (ha w)

variable {E n}

def FE (σ : E ≃ₐ[F] E) (δ : GL (Fin n) E) (Φ : GA E n → ℂ) (x : GA E n) : ℂ :=
  ∫ s : ℝ, Φ (zA E n s * (x⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) x))

end

def QSub : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (H : Subgroup G), IsClosed (H : Set G) → ∀ (μ : Measure H) (j : T →* H) (ν : Measure T), Pair μ j ν →
    ∀ Φ : H → ℂ, Measurable Φ → (∀ t g, Φ (j t * g) = Φ g) →
      quotInt μ (fun x : H => (x : G)) (fun t => (j t : G)) ν Φ = qI μ j ν Φ

def RPF : Prop := ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), RP (pI K n) (pF K n) (KF K n)

def RPE : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ),
    RP (pI E n) (fun v : Pl F => pE E n v) (fun v => KE E n v)

def Compat : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ),
    (∀ g, pI E n (mapGL n (galAd σ) g) = mapGL n (galInf σ) (pI E n g)) ∧
    (∀ (v : Pl F) g, pE E n v (mapGL n (galAd σ) g) = mapGL n (galFin σ v) (pE E n v g)) ∧
    (∀ g, pI E n (mapGL n (adeleMap F E) g) = mapGL n (infMap F E) (pI F n g)) ∧
    (∀ (v : Pl F) g, pE E n v (mapGL n (adeleMap F E) g) = mapGL n (incFin E v) (pF F n v g)) ∧
    (∀ g, mapGL n (galAd σ) (mapGL n (adeleMap F E) g) = mapGL n (adeleMap F E) g) ∧
    (∀ g, mapGL n (galInf σ) (mapGL n (infMap F E) g) = mapGL n (infMap F E) g) ∧
    (∀ δ, mapGL n (galAd σ) (AdelicGLn.diagonal E n δ) = AdelicGLn.diagonal E n (sigmaGL σ δ)) ∧
    ∀ γ, mapGL n (adeleMap F E) (AdelicGLn.diagonal F n γ) = AdelicGLn.diagonal E n (incl γ)

def GalCont : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ),
    Continuous (mapGL n (galAd σ)) ∧ Continuous (mapGL n (galInf σ)) ∧ ∀ v : Pl F, Continuous (mapGL n (galFin σ v))

def LocEmb : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ),
    IsClosedEmbedding (mapGL n (infMap F E)) ∧ ∀ v : Pl F, IsClosedEmbedding (mapGL n (incFin E v))

def UnitIff : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : Pl F) (t : GL (Fin n) (v.adicCompletion F)),
    mapGL n (incFin E v) t ∈ unitSet E n v ↔ t ∈ KF F n v

def CentLoc : Prop := ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (s : {r : ℝ // 0 < r}),
    (∃ r : (InfiniteAdeleRing K)ˣ, ∀ g : GL (Fin n) (InfiniteAdeleRing K),
      ((pI K n (centralSection K n s) * g : GL (Fin n) (InfiniteAdeleRing K)) : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) =
        (r : InfiniteAdeleRing K) • (g : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K))) ∧
    (∀ g, pI K n (centralSection K n s) * g = g * pI K n (centralSection K n s)) ∧
    (∀ v : Pl K, pF K n v (centralSection K n s) = 1) ∧
    ∀ (F : Type) [Field F] [NumberField F] [Algebra F K] (v : Pl F), pE K n v (centralSection K n s) = 1

def CentBC : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (s : {r : ℝ // 0 < r}),
    mapGL n (adeleMap F E) (centralSection F n s) = centralSection E n (s ^ Module.finrank F E)

def ZNorm : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    ∀ (s : ℝ) (δ : GL (Fin n) (InfiniteAdeleRing E)),
      twNorm (mapGL n (galInf σ)) (Module.finrank F E) (pI E n (zA E n s) * δ) =
        mapGL n (infMap F E) (pI F n (zA F n s)) * twNorm (mapGL n (galInf σ)) (Module.finrank F E) δ

def LocNorm : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    ∀ (δ : GL (Fin n) E) (γ : GL (Fin n) F), normGL σ δ = incl γ →
      twNorm (mapGL n (galInf σ)) (Module.finrank F E) (pI E n (AdelicGLn.diagonal E n δ)) =
        mapGL n (infMap F E) (pI F n (AdelicGLn.diagonal F n γ)) ∧
      ∀ v : Pl F, twNorm (mapGL n (galFin σ v)) (Module.finrank F E) (pE E n v (AdelicGLn.diagonal E n δ)) =
        mapGL n (incFin E v) (finAt v (AdelicGLn.diagonal F n γ))

def SepLoc : Prop := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (γ : GL (Fin n) F), IsRegSemisimple γ →
    (pI F n (AdelicGLn.diagonal F n γ)).val.charpoly.Separable ∧
    (∀ s : ℝ, (pI F n (zA F n s) * pI F n (AdelicGLn.diagonal F n γ)).val.charpoly.Separable) ∧
    ∀ v : Pl F, (finAt v (AdelicGLn.diagonal F n γ)).val.charpoly.Separable

def TComm : Prop := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (γ : GL (Fin n) F), IsRegSemisimple γ →
    (∀ s t : TA γ, s * t = t * s) ∧ (∀ s t : TI γ, s * t = t * s) ∧ (∀ v : Pl F, ∀ s t : TF γ v, s * t = t * s) ∧
    ∀ γ₁ : G1 F n, (γ₁ : GA F n) = AdelicGLn.diagonal F n γ → ∀ s t : Subgroup.centralizer {γ₁}, s * t = t * s

def Triv : Prop := ∀ (F : Type) [Field F] [NumberField F],
    galInf (1 : F ≃ₐ[F] F) = RingHom.id _ ∧ infMap F F = RingHom.id _ ∧
    ∀ v : Pl F, galFin (1 : F ≃ₐ[F] F) v = RingHom.id _ ∧ Function.Bijective (incFin F v)

def BoundE : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    ∀ (δ : GL (Fin n) (InfiniteAdeleRing E)) (D : Set (GL (Fin n) (InfiniteAdeleRing E))), IsCompact D →
      ∃ B : Set ℝ, IsCompact B ∧ ∀ s x, pI E n (zA E n s) * (x⁻¹ * δ * mapGL n (galInf σ) x) ∈ D → s ∈ B

def InfF : Prop := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n → ∀ γ : GL (Fin n) (InfiniteAdeleRing F),
    (∀ D : Set (GL (Fin n) (InfiniteAdeleRing F)), IsCompact D →
      ∃ B : Set ℝ, IsCompact B ∧ ∀ s x, pI F n (zA F n s) * (x⁻¹ * γ * x) ∈ D → s ∈ B) ∧
    (γ.val.charpoly.Separable → ∀ D : Set (GL (Fin n) (InfiniteAdeleRing F)), IsCompact D →
      ∃ C, IsCompact C ∧ ∀ x, x⁻¹ * γ * x ∈ D → ∃ t, t * γ = γ * t ∧ ∃ y ∈ C, x = t * y)

def SelmerRankBoundLaurent : Prop := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n → ∀ γ : GL (Fin n) F, IsRegSemisimple γ →
    ∀ᶠ v : Pl F in cofinite, ∀ x : GL (Fin n) (v.adicCompletion F),
      x⁻¹ * finAt v (AdelicGLn.diagonal F n γ) * x ∈ KF F n v ↔
      ∃ t, t * finAt v (AdelicGLn.diagonal F n γ) = finAt v (AdelicGLn.diagonal F n γ) * t ∧ ∃ y ∈ KF F n v, x = t * y

def Spl : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    (∃ e : G1 E n × {r : ℝ // 0 < r} ≃ₜ* GA E n, ∀ x, e x = (x.1 : GA E n) * mapGL n (adeleMap F E) (centralSection F n x.2)) ∧
    ∀ (γ : GL (Fin n) F) (γ₁ : G1 F n), (γ₁ : GA F n) = AdelicGLn.diagonal F n γ →
      (∃ e : Subgroup.centralizer {γ₁} × {r : ℝ // 0 < r} ≃ₜ* TA γ,
        ∀ x, (e x : GA F n) = ((x.1 : G1 F n) : GA F n) * centralSection F n x.2) ∧
      ∃ j : Subgroup.centralizer {γ₁} →* G1 E n, IsClosedEmbedding j ∧
        ∀ t, (j t : GA E n) = mapGL n (adeleMap F E) ((t : G1 F n) : GA F n)

def Glob : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    ∀ (μE : Measure (G1 E n)) (μF : Measure (G1 F n)), μE.IsHaarMeasure → μF.IsHaarMeasure →
    ∃ (μE' : Measure (GA E n)) (μF' : Measure (GA F n)), Uni μE' ∧ Uni μF' ∧
      ∀ (γ : GL (Fin n) F) (γ₁ : G1 F n), (γ₁ : GA F n) = AdelicGLn.diagonal F n γ → IsRegSemisimple γ →
      ∀ ν : Measure (Subgroup.centralizer {γ₁}), ν.IsHaarMeasure → ∃ ν' : Measure (TA γ), ν'.IsHaarMeasure ∧
        (∀ Φ : GA F n → ℂ, Measurable (FF γ Φ) →
          quotInt μF id (fun t : Subgroup.centralizer {γ₁} => (t : G1 F n)) ν (fun x => avg Φ (x⁻¹ * γ₁ * x)) =
            qI μF' (TA γ).subtype ν' (FF γ Φ)) ∧
        ∀ δ : GL (Fin n) E, normGL σ δ = incl γ → ∀ Φ : GA E n → ℂ, Measurable (FE σ δ Φ) →
          quotInt μE (fun x : G1 E n => (x : GA E n))
            (fun t : Subgroup.centralizer {γ₁} => mapGL n (adeleMap F E) ((t : G1 F n) : GA F n)) ν
            (fun x => ext0 (avg Φ) ((x : GA E n)⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) (x : GA E n))) =
            qI μE' ((mapGL n (adeleMap F E)).comp (TA γ).subtype) ν' (FE σ δ Φ)

def SideF : Prop := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n →
    ∀ [MeasurableSpace (GL (Fin n) (InfiniteAdeleRing F))] [BorelSpace (GL (Fin n) (InfiniteAdeleRing F))]
      [∀ v : Pl F, MeasurableSpace (GL (Fin n) (v.adicCompletion F))] [∀ v : Pl F, BorelSpace (GL (Fin n) (v.adicCompletion F))]
      (μ : Measure (GA F n)) (μi : Measure (GL (Fin n) (InfiniteAdeleRing F))) (m : ∀ v : Pl F, Measure (GL (Fin n) (v.adicCompletion F))),
      Uni μ → μi.IsHaarMeasure → (∀ v, (m v).IsHaarMeasure) → ∀ γ : GL (Fin n) F, IsRegSemisimple γ →
      ∀ (ν : Measure (TA γ)) (νi : Measure (TI γ)) (nv : ∀ v : Pl F, Measure (TF γ v)),
      ν.IsHaarMeasure → νi.IsHaarMeasure → (∀ v, (nv v).IsHaarMeasure) → ∀ (S : Finset (Pl F)) (a b : NNReal), a ≠ 0 → b ≠ 0 →
      EulT γ ν νi nv b S → Eul (pI F n) (pF F n) (KF F n) μ μi m a S →
      ∀ (fi : GL (Fin n) (InfiniteAdeleRing F) → ℂ) (f : ∀ v : Pl F, GL (Fin n) (v.adicCompletion F) → ℂ),
      Continuous fi → HasCompactSupport fi → (∀ v, Continuous (f v)) →
      (∀ v ∉ S, f v = (KF F n v : Set _).indicator 1 ∧ ∀ x : GL (Fin n) (v.adicCompletion F),
        x⁻¹ * finAt v (AdelicGLn.diagonal F n γ) * x ∈ KF F n v ↔
        ∃ t, t * finAt v (AdelicGLn.diagonal F n γ) = finAt v (AdelicGLn.diagonal F n γ) * t ∧ ∃ y ∈ KF F n v, x = t * y) →
      Measurable (FF γ (tensF fi f)) ∧ qI μ (TA γ).subtype ν (FF γ (tensF fi f)) =
        ((a : ℝ) : ℂ) / ((b : ℝ) : ℂ) *
          (∫ s : ℝ, qI μi (TI γ).subtype νi fun x => fi (x⁻¹ * (pI F n (zA F n s) * pI F n (AdelicGLn.diagonal F n γ)) * x)) *
          ∏ v ∈ S, qI (m v) (TF γ v).subtype (nv v) fun x => f v (x⁻¹ * finAt v (AdelicGLn.diagonal F n γ) * x)

def SideE : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    ∀ [MeasurableSpace (GL (Fin n) (InfiniteAdeleRing F))] [BorelSpace (GL (Fin n) (InfiniteAdeleRing F))]
      [∀ v : Pl F, MeasurableSpace (GL (Fin n) (v.adicCompletion F))] [∀ v : Pl F, BorelSpace (GL (Fin n) (v.adicCompletion F))]
      [MeasurableSpace (GL (Fin n) (InfiniteAdeleRing E))] [BorelSpace (GL (Fin n) (InfiniteAdeleRing E))]
      [∀ v : Pl F, MeasurableSpace (GL (Fin n) (CompletionsOver E v))] [∀ v : Pl F, BorelSpace (GL (Fin n) (CompletionsOver E v))]
      (μ : Measure (GA E n)) (μi : Measure (GL (Fin n) (InfiniteAdeleRing E))) (m : ∀ v : Pl F, Measure (GL (Fin n) (CompletionsOver E v))),
      Uni μ → μi.IsHaarMeasure → (∀ v, (m v).IsHaarMeasure) → ∀ γ : GL (Fin n) F, IsRegSemisimple γ →
      ∀ δ : GL (Fin n) E, normGL σ δ = incl γ →
      ∀ (ν : Measure (TA γ)) (νi : Measure (TI γ)) (nv : ∀ v : Pl F, Measure (TF γ v)),
      ν.IsHaarMeasure → νi.IsHaarMeasure → (∀ v, (nv v).IsHaarMeasure) → ∀ (S : Finset (Pl F)) (a b : NNReal), a ≠ 0 → b ≠ 0 →
      EulT γ ν νi nv b S → Eul (pI E n) (fun v : Pl F => pE E n v) (fun v => KE E n v) μ μi m a S →
      ∀ (φi : GL (Fin n) (InfiniteAdeleRing E) → ℂ) (φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ),
      Continuous φi → HasCompactSupport φi → (∀ v, Continuous (φ v)) →
      (∀ v ∉ S, φ v = (unitSet E n v).indicator 1 ∧ ∀ x : GL (Fin n) (CompletionsOver E v),
        x⁻¹ * mapGL n (atFin v) (AdelicGLn.diagonal E n δ) * mapGL n (galFin σ v) x ∈ unitSet E n v ↔
        ∃ t : GL (Fin n) (v.adicCompletion F), t * finAt v (AdelicGLn.diagonal F n γ) = finAt v (AdelicGLn.diagonal F n γ) * t ∧
          ∃ y ∈ unitSet E n v, x = mapGL n (incFin E v) t * y) →
      Measurable (FE σ δ (tensE φi φ)) ∧ qI μ ((mapGL n (adeleMap F E)).comp (TA γ).subtype) ν (FE σ δ (tensE φi φ)) =
        ((a : ℝ) : ℂ) / ((b : ℝ) : ℂ) *
          (∫ s : ℝ, qI μi ((mapGL n (infMap F E)).comp (TI γ).subtype) νi fun x =>
            φi (x⁻¹ * (pI E n (zA E n s) * pI E n (AdelicGLn.diagonal E n δ)) * mapGL n (galInf σ) x)) *
          ∏ v ∈ S, qI (m v) ((mapGL n (incFin E v)).comp (TF γ v).subtype) (nv v) fun x =>
            φ v (x⁻¹ * pE E n v (AdelicGLn.diagonal E n δ) * mapGL n (galFin σ v) x)

end UpperTheory.ConvolutionTheory.T4
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.UnitaryGroupGeometricSideOfQuotientIdentities
section
open PositivityTheory.Rg.Tf.Geo

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.RightCosetSpace
open scoped ENNReal

private theorem UpperTheory.ConvolutionTheory.G.stage_key
    {X T : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group T] [TopologicalSpace T]
    [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (μ : Measure X) [μ.IsHaarMeasure]
    (ν : Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant] (i : T →* X) (hi : Continuous i)
    (hinj : Function.Injective i) (Λ : Subgroup T) [DiscreteTopology Λ] (Γ₀ : Subgroup X)
    [DiscreteTopology Γ₀] (hΛ : Λ.map i = Γ₀)
    (ρ : X → ℝ≥0∞) (hρ : Measurable ρ) (hρ1 : ∀ x, ∫⁻ t, ρ (i t * x) ∂ν = 1)
    (F : X → ℝ≥0∞) (hF : Measurable F) (hFi : ∀ t x, F (i t * x) = F x) :
    ∫⁻ x in fundamentalDomain Γ₀, F x ∂μ = ν (fundamentalDomain Λ) * ∫⁻ x, F x * ρ x ∂μ := by
  subst hΛ
  set D := fundamentalDomain Λ with hDdef
  set E := fundamentalDomain (Λ.map i) with hEdef
  have hD : IsFundamentalDomain Λ D ν := isFundamentalDomain_fundamentalDomain Λ ν
  have hE : IsFundamentalDomain (Λ.map i) E μ := isFundamentalDomain_fundamentalDomain _ μ
  have hc : Continuous fun p : X × T => i p.2⁻¹ * p.1 :=
    (hi.comp continuous_snd.inv).mul continuous_fst
  have hm : Measurable fun p : X × T => ρ (i p.2⁻¹ * p.1) := hρ.comp hc.measurable
  set ρ' : X → ℝ≥0∞ := fun x => ∫⁻ d in D, ρ (i d⁻¹ * x) ∂ν with hρ'
  have hρ'm : Measurable ρ' := hm.lintegral_prod_right'
  have hinv : ∀ x, ∫⁻ d, ρ (i d⁻¹ * x) ∂ν = 1 := fun x => by
    rw [← hρ1 x]
    exact lintegral_inv_eq_self (fun t => ρ (i t * x))
  have hsum : ∀ x, ∑' l : Λ, ρ' (i l * x) = 1 := fun x => by
    rw [← hinv x, hD.lintegral_eq_tsum']
    refine tsum_congr fun l => ?_
    simp only [hρ']
    refine lintegral_congr fun d => ?_
    simp [Subgroup.smul_def, mul_assoc]
  have hunf : ∫⁻ x, F x * ρ' x ∂μ = ∫⁻ x in E, F x ∂μ := by
    rw [hE.lintegral_eq_tsum'', ← lintegral_tsum]
    · refine lintegral_congr fun x => ?_
      rw [← (Subgroup.equivMapOfInjective Λ i hinj).toEquiv.tsum_eq]
      have : ∀ l : Λ, F ((Subgroup.equivMapOfInjective Λ i hinj).toEquiv l • x) *
          ρ' ((Subgroup.equivMapOfInjective Λ i hinj).toEquiv l • x) = F x * ρ' (i l * x) := fun l => by
        have h : (Subgroup.equivMapOfInjective Λ i hinj).toEquiv l • x = i l * x := rfl
        rw [h, hFi]
      simp only [this]
      rw [ENNReal.tsum_mul_left, hsum, mul_one]
    · intro g
      exact ((hF.mul hρ'm).comp (measurable_const_smul g)).aemeasurable
  have hfub : ∫⁻ x, F x * ρ' x ∂μ = ν D * ∫⁻ x, F x * ρ x ∂μ := by
    have h1 : ∀ x, F x * ρ' x = ∫⁻ d in D, F x * ρ (i d⁻¹ * x) ∂ν := fun x => by
      have hd : Measurable fun d : T => ρ (i d⁻¹ * x) :=
        hρ.comp ((hi.comp continuous_inv).mul continuous_const).measurable
      rw [lintegral_const_mul _ hd]
    simp only [h1]
    rw [lintegral_lintegral_swap]
    · have h2 : ∀ d : T, ∫⁻ x, F x * ρ (i d⁻¹ * x) ∂μ = ∫⁻ x, F x * ρ x ∂μ := fun d => by
        rw [← lintegral_mul_left_eq_self (fun y => F y * ρ y) (i d⁻¹)]
        refine lintegral_congr fun x => ?_
        rw [hFi]
      simp only [h2]
      rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]
    · exact ((hF.comp measurable_fst).mul hm).aemeasurable
  rw [← hunf, hfub]

theorem UpperTheory.ConvolutionTheory.G.unitaryGroupGeometricSide_of_quotient_identities :
    Q1 → Q2 → U2 := by
  intro hQ1 hQ2 X T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ _ i hi Λ _ Γ₀ _ hΛ hvol Φ hΦc hΦi hint
  have hD : IsFundamentalDomain Λ (fundamentalDomain Λ) ν := isFundamentalDomain_fundamentalDomain Λ ν
  have hvolD : quotientMeasure Λ ν Set.univ = ν (fundamentalDomain Λ) := quotientMeasure_univ ν hD
  have hD0 : ν (fundamentalDomain Λ) ≠ 0 := hD.measure_ne_zero (NeZero.ne ν)
  have hΦm : Measurable Φ := hΦc.measurable
  have hic : Continuous i := hi.continuous
  have hout : ∀ g, Φ (Quotient.out (RightCosetSpace.mk Γ₀ g)) = Φ g := fun g => by
    obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1 (Quotient.out_eq (RightCosetSpace.mk Γ₀ g))
    have hγm : (γ : X) ∈ Λ.map i := hΛ ▸ γ.2
    obtain ⟨t, -, ht⟩ := Subgroup.mem_map.1 hγm
    rw [← hγ, Subgroup.smul_def, smul_eq_mul, ← ht, hΦi]
  have key := fun ρ hρ hρ1 F hF hFi =>
    UpperTheory.ConvolutionTheory.G.stage_key μ ν i hic hi.injective Λ Γ₀ hΛ ρ hρ hρ1 F hF hFi
  have hEfin : ∫⁻ x in fundamentalDomain Γ₀, ‖Φ x‖ₑ ∂μ < ⊤ := by
    have h := hint.2
    rw [HasFiniteIntegral, lintegral_quotientMeasure] at h
    simpa only [hout] using h
  have hfin : ∀ ρ, IsNormAlong id i ν ρ → ∫⁻ x, ‖Φ x‖ₑ * ρ x ∂μ < ⊤ := fun ρ hρ => by
    have h := key ρ hρ.1 hρ.2 (fun x => ‖Φ x‖ₑ) hΦm.enorm (fun t x => by simp only [hΦi])
    rw [h] at hEfin
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc, ENNReal.mul_top hD0] at hEfin
    exact lt_irrefl _ hEfin
  refine ⟨?_, hfin⟩
  obtain ⟨ρ₀, hρc, hρn, -⟩ := hQ2 X T ν i hi
  have e1 := hQ1 X X T μ ν (MonoidHom.id X) i measurable_id hic Φ (fun x => (ρ₀ x : ℝ≥0∞)) hΦm hΦi hρn (hfin _ hρn)
  have hmeas : (μ.restrict (fundamentalDomain Γ₀)).map Φ =
      (ν (fundamentalDomain Λ) • μ.withDensity (fun x => (ρ₀ x : ℝ≥0∞))).map Φ := by
    rw [Measure.ext_iff_lintegral]
    intro f hf
    have hw : ∫⁻ a, f (Φ a) ∂μ.withDensity (fun x => (ρ₀ x : ℝ≥0∞)) =
        ∫⁻ a, f (Φ a) * (ρ₀ a : ℝ≥0∞) ∂μ := by
      rw [show (fun a => f (Φ a)) = f ∘ Φ from rfl,
        lintegral_withDensity_eq_lintegral_mul μ hρn.1 (hf.comp hΦm)]
      exact lintegral_congr fun a => mul_comm _ _
    rw [lintegral_map hf hΦm, lintegral_map hf hΦm, lintegral_smul_measure, hw, smul_eq_mul]
    exact key _ hρn.1 hρn.2 (fun x => f (Φ x)) (hf.comp hΦm) (fun t x => by simp only [hΦi])
  have hq : ∫ y, Φ (Quotient.out y) ∂quotientMeasure Γ₀ μ = ∫ g in fundamentalDomain Γ₀, Φ g ∂μ := by
    rw [integral_quotientMeasure]
    simp only [hout]
  have hz : ∫ g in fundamentalDomain Γ₀, Φ g ∂μ =
      ∫ x, Φ x ∂(ν (fundamentalDomain Λ) • μ.withDensity (fun x => (ρ₀ x : ℝ≥0∞))) := by
    have h1 : ∀ m : Measure X, ∫ z, z ∂(m.map Φ) = ∫ x, Φ x ∂m := fun m =>
      integral_map hΦm.aemeasurable aestronglyMeasurable_id
    rw [← h1, ← h1, hmeas]
  rw [hq, hz, integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hρn.1
    (Filter.Eventually.of_forall fun x => ENNReal.coe_lt_top), hvolD, Complex.real_smul]
  congr 1
  have e2 : quotInt μ id i ν Φ = ∫ x, Φ x * (((ρ₀ x : ℝ≥0∞)).toReal : ℂ) ∂μ := e1
  rw [e2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [Complex.real_smul, mul_comm]
end

