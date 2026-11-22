import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIndepBridge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0563
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0109
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0452
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionsSpanFullLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibility
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0220
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0571
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0405
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0409
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0361
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0373
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDiagTangentUnitFrameHolomorphicArcLe
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0570
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0573
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemClosureOfJumps
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

namespace GlobalTheory.HodgeTateCochar

theorem poly_vanish : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL K'' : FinExt l) (m : ℕ) (r₁ : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1),
    LL.1 ≤ K''.1 → K.1 ≤ K''.1 → ∀ (Pm : Matrix.GeneralLinearGroup (Fin m) ℂ_[l]) (k : Fin m → ℤ),
    (∀ g : ↥(GK K), (g : GQ l) ∈ GK K'' →
      (r₁ g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) *
        (Pm : Matrix (Fin m) (Fin m) ℂ_[l]).map (Per.σC (g : GQ l)) =
      (Pm : Matrix (Fin m) (Fin m) ℂ_[l]) *
        Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]))) →
    ∀ f : MvPolynomial (Fin m × Fin m) ℂ_[l],
    (∀ g : ↥(GK K), (g : GQ l) ∈ GK K'' →
      MvPolynomial.eval (fun ij => ((((r₁ g : Matrix (Fin m) (Fin m) ↥LL.1) ij.1 ij.2 : ↥LL.1) : Om l) : ℂ_[l])) f = 0) →
    ∀ t : ℂ_[l], t ≠ 0 →
      MvPolynomial.eval (fun ij => ((Pm : Matrix (Fin m) (Fin m) ℂ_[l]) * Matrix.diagonal (fun i => t ^ k i) *
        ((Pm⁻¹ : Matrix.GeneralLinearGroup (Fin m) ℂ_[l]) : Matrix (Fin m) (Fin m) ℂ_[l])) ij.1 ij.2) f = 0 := by
  intro l _ P AI hT K LL K'' m r₁ hLL hK Pm k heig f hf t ht
  letI act : MulSemiringAction ↥(GK K'') ℂ_[l] :=
    { smul := fun g x => Per.σC (g : GQ l) x
      one_smul := fun x => GlobalTheory.RingBasics.σC_one x
      mul_smul := fun g h x => GlobalTheory.RingBasics.σC_mul (g : GQ l) (h : GQ l) x
      smul_zero := fun g => map_zero (Per.σC (g : GQ l))
      smul_add := fun g x y => map_add (Per.σC (g : GQ l)) x y
      smul_one := fun g => map_one (Per.σC (g : GQ l))
      smul_mul := fun g x y => map_mul (Per.σC (g : GQ l)) x y }
  let χ : ↥(GK K'') →* ℂ_[l]ˣ :=
    ((Units.map (algebraMap ℚ_[l] ℂ_[l]).toMonoidHom).comp (P.χQ.comp (GK K'').subtype))⁻¹
  have hχ : ∀ (g : ↥(GK K'')) (n : ℤ), ((χ g ^ n : ℂ_[l]ˣ) : ℂ_[l]) =
      ((((P.χQ (g : GQ l)) ^ (-n) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) := by
    intro g n
    have e : χ g ^ n = Units.map (algebraMap ℚ_[l] ℂ_[l]).toMonoidHom (P.χQ (g : GQ l) ^ (-n)) := by
      rw [map_zpow]
      simp [χ, zpow_neg, inv_zpow']
    rw [e]
    rfl
  let φ : ↥LL.1 →+* ℂ_[l] := (UniformSpace.Completion.coeRingHom).comp (algebraMap ↥LL.1 (Om l))
  let ρ : ↥(GK K'') →* Matrix.GeneralLinearGroup (Fin m) ℂ_[l] :=
    (mapRep φ r₁).comp (Subgroup.inclusion (GK_le hK))
  have hρ : ∀ (γ : ↥(GK K'')) i j, (ρ γ : Matrix (Fin m) (Fin m) ℂ_[l]) i j =
      ((((r₁ (Subgroup.inclusion (GK_le hK) γ) : Matrix (Fin m) (Fin m) ↥LL.1) i j : ↥LL.1) : Om l) : ℂ_[l]) :=
    fun _ _ _ => rfl
  have key := GlobalTheory.T.vanish_at_hodgeTate_cocharacter (C := ℂ_[l]) (Γ := ↥(GK K'')) (n := Fin m) χ ?_ ρ ?_ Pm k ?_ f ?_ (Units.mk0 t ht)
  · simpa [Units.val_zpow_eq_zpow_val] using key
  · intro n hn x H
    refine GlobalTheory.T.tate_no_twisted_invariants_complexPadic l P AI hT K'' (-n) (neg_ne_zero.mpr hn) x fun g => ?_
    exact (H g).trans (by rw [hχ])
  · intro g γ i j
    change Per.σC (g : GQ l) _ = _
    rw [hρ, GlobalTheory.RingBasics.σC_coe]
    congr 1
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (hLL (r₁ _ i j).2)
  · intro g
    have h1 := heig (Subgroup.inclusion (GK_le hK) g) g.2
    change (ρ g : Matrix (Fin m) (Fin m) ℂ_[l]) * (Pm : Matrix (Fin m) (Fin m) ℂ_[l]).map (Per.σC (g : GQ l)) = _
    simp only [hχ]
    exact h1
  · intro γ
    exact hf _ γ.2

theorem mem_closure_of_jumps : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) {a : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin a) (Om l)) (τ : E →+* Om l) (J : Multiset ℤ), GlobalTheory.Pst.IsJumpsAt P Bw r τ J → Multiset.card J = a → ∃ (Pm : Matrix.GeneralLinearGroup (Fin a) ℂ_[l]) (k : Fin a → ℤ), Multiset.map k Finset.univ.val = J ∧ ∀ (K' : FinExt l), Bw.Kw.1 ≤ K'.1 → ∀ f : MvPolynomial (Fin a × Fin a) ℂ_[l], (∀ g : ↥Gw, ((Bw.e g : ↥(GK Bw.Kw)) : GQ l) ∈ GK K' → MvPolynomial.eval (fun ij => (((r g : Matrix (Fin a) (Fin a) (Om l)) ij.1 ij.2 : Om l) : ℂ_[l])) f = 0) → ∀ t : ℂ_[l], t ≠ 0 → MvPolynomial.eval (fun ij => ((Pm : Matrix (Fin a) (Fin a) ℂ_[l]) * Matrix.diagonal (fun i => t ^ k i) * ((Pm⁻¹ : Matrix.GeneralLinearGroup (Fin a) ℂ_[l]) : Matrix (Fin a) (Fin a) ℂ_[l])) ij.1 ij.2) f = 0 := by
  intro l _ P AI hT E Ω _ _ _ _ Gw O _ _ _ Bw a r τ J hJ hcard
  obtain ⟨LL', r', ⟨hLL, hmod⟩, hdR, τ', -, hcnt⟩ := hJ
  haveI := Bw.Kw.2
  haveI := LL'.2

  let τo : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l := LL'.1.val.comp τ'
  let g : GQ l := AlgEquiv.ofBijective (τo.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _)
  have hg : ∀ x : ↥Bw.Kw.1, g (x : Om l) = ((τ' x : ↥LL'.1) : Om l) := fun x => τo.liftNormal_commutes (Om l) x

  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : FinExt l, K₁.1 = Bw.Kw.1.map (g : Om l →ₐ[ℚ_[l]] Om l) :=
    ⟨⟨Bw.Kw.1.map (g : Om l →ₐ[ℚ_[l]] Om l),
      LinearEquiv.finiteDimensional (IntermediateField.equivMap Bw.Kw.1 (g : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv⟩, rfl⟩
  have hK : ∀ x, x ∈ Bw.Kw.1 ↔ g x ∈ K₁.1 := GlobalTheory.Pst.BridgeInd.mem_iff_of_map_eq hK₁
  have hK₁LL : K₁.1 ≤ LL'.1 := by
    rw [hK₁]
    rintro _ ⟨x, hx, rfl⟩
    have := hg ⟨x, hx⟩
    simp only at this
    change g x ∈ LL'.1
    rw [this]; exact (τ' ⟨x, hx⟩).2

  let cj : ↥(GK K₁) →* ↥(GK Bw.Kw) :=
    { toFun := fun h => ⟨g⁻¹ * (h : GQ l) * g, GlobalTheory.Pst.BridgeInd.mem_GK_conj_inv hK h.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun h₁ h₂ => Subtype.ext (by simp [mul_assoc]) }
  let r₀ : ↥(GK Bw.Kw) →* Matrix.GeneralLinearGroup (Fin a) ↥LL'.1 := r'.comp Bw.e.symm.toMonoidHom
  let r₁ : ↥(GK K₁) →* Matrix.GeneralLinearGroup (Fin a) ↥LL'.1 := r₀.comp cj
  have hρ : ∀ (h : ↥(GK Bw.Kw)) (h' : ↥(GK K₁)), (h' : GQ l) = g * h * g⁻¹ →
      (((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥LL'.1 ≃ₐ[↥LL'.1] _) : _ →* _).comp
        ((Units.coeHom _).comp r₁)) h' = Bw.repE LL' r' h := by
    intro h h' hh
    have : cj h' = h := Subtype.ext (by simp [cj, hh, mul_assoc])
    simp only [MonoidHom.comp_apply, r₁, this]
    rfl
  have hD := GlobalTheory.Pst.BridgeInd.finrank_DdR_conj P hρ hK
  have hdR₁ : Module.finrank ↥LL'.1 ↥(DdR (P.PD K₁) (LL := ↥LL'.1) (V := Fin a → ↥LL'.1) (((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥LL'.1 ≃ₐ[↥LL'.1] _) : _ →* _).comp
        ((Units.coeHom _).comp r₁))) = Module.finrank ℚ_[l] ↥K₁.1 * a := by
    rw [← hD, ← GlobalTheory.Pst.BridgeInd.finrank_eq_of_mem_iff_field hK]
    exact hdR
  let τ₂ : ↥K₁.1 →ₐ[ℚ_[l]] ↥LL'.1 := IntermediateField.inclusion hK₁LL
  have hτ₂ : ∀ x : ↥K₁.1, ((τ₂ x : ↥LL'.1) : Om l) = (x : Om l) := fun x => rfl
  have hM : ∀ n, multV (P.PD Bw.Kw) (Bw.repE LL' r') τ' n = multV (P.PD K₁) _ τ₂ n :=
    fun n => GlobalTheory.Pst.BridgeInd.multV_conj P hρ hK τ' τ₂ (fun c c' hc => Subtype.ext (by
      change (c' : Om l) = _; rw [hc, hg])) n
  have hsplit : ∀ (σ : ↥K₁.1 →ₐ[ℚ_[l]] Om l) (x : ↥K₁.1), σ x ∈ LL'.1 := by
    intro σ x
    have hx : g⁻¹ (x : Om l) ∈ Bw.Kw.1 := (hK _).2 (by simp)
    let e₁ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥K₁.1 :=
      ((g : Om l →ₐ[ℚ_[l]] Om l).comp Bw.Kw.1.val).codRestrict K₁.1.toSubalgebra fun c => (hK _).1 c.2
    have he : e₁ ⟨g⁻¹ (x : Om l), hx⟩ = x := Subtype.ext (by
      change g (g⁻¹ (x : Om l)) = (x : Om l)
      rw [← AlgEquiv.mul_apply, mul_inv_cancel]; rfl)
    rw [← he]
    exact hLL (Bw.LL_split (σ.comp e₁) ⟨g⁻¹ (x : Om l), hx⟩)
  haveI := K₁.2
  let K₀ : FinExt l := ⟨K₁.1 ⊔ LL'.1, inferInstance⟩
  obtain ⟨Pm, k, hk, heig⟩ := GlobalTheory.T.deRham_exists_hodgeTate_eigenbasis l P AI hT K₁ LL' a r₁ hdR₁ hsplit τ₂ hτ₂ K₀
    le_sup_left le_sup_right
  refine ⟨Pm, k, ?_, ?_⟩
  · refine Multiset.ext.mpr fun n => ?_
    have := (hk n).trans ((hM n).symm.trans (hcnt n).symm)
    exact_mod_cast this
  intro K' hK' f hf t ht
  haveI := K'.2
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : FinExt l, K₂.1 = K'.1.map (g : Om l →ₐ[ℚ_[l]] Om l) :=
    ⟨⟨K'.1.map (g : Om l →ₐ[ℚ_[l]] Om l),
      LinearEquiv.finiteDimensional (IntermediateField.equivMap K'.1 (g : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv⟩, rfl⟩
  have hK' : ∀ x, x ∈ K'.1 ↔ g x ∈ K₂.1 := GlobalTheory.Pst.BridgeInd.mem_iff_of_map_eq hK₂
  haveI := K₂.2
  let K'' : FinExt l := ⟨K₂.1 ⊔ K₀.1, inferInstance⟩
  refine poly_vanish l P AI hT K₁ LL' K'' a r₁ (le_trans le_sup_right le_sup_right)
    (le_trans le_sup_left le_sup_right) Pm k (fun h hh => heig h (GK_le le_sup_right hh)) f ?_ t ht
  intro h hh
  have h2 : (h : GQ l) ∈ GK K₂ := GK_le le_sup_left hh
  have h3 : ((cj h : ↥(GK Bw.Kw)) : GQ l) ∈ GK K' := GlobalTheory.Pst.BridgeInd.mem_GK_conj_inv hK' h2
  have h4 := hf (Bw.e.symm (cj h)) (by simpa using h3)
  rw [← hmod] at h4
  exact h4

end GlobalTheory.HodgeTateCochar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachNIffExpansion
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.WachModulePoleQuotient

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem mem_N_iff_of_points (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) {ι : Type} [Fintype ι]
    (nb : Module.Basis ι (LetA O n) ↥(W.N T)) (P : ZMod n → LL → Prop) (Φ : ZMod n → LL → Prop)
    (k : ℕ) (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T)
    (hkey : ∀ i ζ, P i ζ → (Φ i ζ ↔ ∀ j, nb.repr ⟨W.Q ^ k • x, hx⟩ j ∈ van W i ζ k))
    (hQ : ∀ i ζ, P i ζ → ∃ w : PowerSeries LL, W.lev i ζ W.Q = PowerSeries.X * w)
    (hdiv : ∀ a : LetA O n, (∀ i ζ, P i ζ → a ∈ van W i ζ k) → W.Q ^ k ∣ a)
    (hunit : IsUnit (algebraMap (LetA O n) W.EE W.Q)) :
    x ∈ W.N T ↔ ∀ i ζ, P i ζ → Φ i ζ := by
  constructor
  · intro hxN i ζ hζ
    rw [hkey i ζ hζ]
    intro j
    have e : (⟨W.Q ^ k • x, hx⟩ : ↥(W.N T)) = W.Q ^ k • (⟨x, hxN⟩ : ↥(W.N T)) := rfl
    rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]
    obtain ⟨w, hw⟩ := hQ i ζ hζ
    refine Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 ?_)
    rw [map_mul, map_pow, hw]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (dvd_mul_right _ _) k) _
  · intro H
    have hd : ∀ j, W.Q ^ k ∣ nb.repr ⟨W.Q ^ k • x, hx⟩ j := fun j =>
      hdiv _ (fun i ζ hζ => (hkey i ζ hζ).1 (H i ζ hζ) j)
    choose b hb using hd
    let z : ↥(W.N T) := ∑ j, b j • nb j
    have hz : W.Q ^ k • ((z : ↥(W.N T)) : W.DD T) = W.Q ^ k • x := by
      have e : (⟨W.Q ^ k • x, hx⟩ : ↥(W.N T)) = W.Q ^ k • z := by
        conv_lhs => rw [← nb.sum_repr ⟨W.Q ^ k • x, hx⟩]
        simp only [z, Finset.smul_sum, hb, mul_smul]
      exact (congrArg Subtype.val e).symm
    have hu : IsUnit (algebraMap (LetA O n) W.EE (W.Q ^ k)) := by
      rw [map_pow]
      exact hunit.pow k
    obtain ⟨u, hu'⟩ := hu
    have h1 : ∀ y : W.DD T, W.Q ^ k • y = (u : W.EE) • y := fun y => by
      rw [hu', algebraMap_smul]
    rw [h1, h1] at hz
    have hx' : x = (z : W.DD T) := by
      have := congrArg (fun y => ((u⁻¹ : W.EEˣ) : W.EE) • y) hz
      simp only [smul_smul, Units.inv_mul, one_smul] at this
      exact this.symm
    rw [hx']
    exact z.2

end Generic

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem mem_N_iff_expansion : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (k : ℕ) (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T), x ∈ W.N T ↔ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ f ∈ Lat C h T i ζ, ∀ j : ℤ, ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ j = f (j - k) := by
  intro D HW F Cm l _ K s LL h W C T hT k x hx
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  refine mem_N_iff_of_points W T nb (fun i ζ => IsPrimitiveRoot ζ (l ^ s)) _ k x hx ?_ ?_ ?_ ?_
  · intro i ζ hζ
    exact ((GlobalTheory.NL.LevInj.expansion_basis D HW F Cm l K s LL h T hT i ζ ⟨s, hζ⟩
      (GlobalTheory.NL.FullLevel.full_lat D HW F Cm l K s LL h T hT i ζ hζ)).2 _ nb).2.2 _ k
  · intro i ζ hζ
    obtain ⟨⟨w, _, hw⟩, -⟩ := (GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ ⟨s, hζ⟩).2.2.2.1 hζ
    exact ⟨w, hw⟩
  · exact (GlobalTheory.NL.WDiv.weierstrass_dense D HW l K s LL h).1 k
  · have h0 := ((GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.2 0).2
    simpa using h0

end GlobalTheory.NL.WachModulePoleQuotient
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MinJumpSumLeOfPowMemOfInertiaEqTop
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem min_jumpSum_le_of_pow_mem_of_inertia_eq_top : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E : ℕ) (B C : Subgroup (L ≃ₐ[F] L)), lowerRamificationGroup F L 0 = ⊤ → OrdIs L p E → (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → (∀ σ : L ≃ₐ[F] L, σ ^ p ∈ C → σ ∈ B) → min (2 * jumpSum (wild F L) ⊤ B) (jumpSum (wild F L) ⊤ B + E) ≤ jumpSum (wild F L) ⊤ C := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E B C h0 hE hcomm hpow
  by_cases hB : B = ⊤
  ·
    subst hB
    have hzero : jumpSum (wild F L) ⊤ (⊤ : Subgroup (L ≃ₐ[F] L)) = 0 := by
      simp [jumpSum]
    simp [hzero]
  ·
    obtain ⟨e, he, hEe, hram⟩ := GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension F L p E hE
    have hcard : ramificationIndex F L = Nat.card (L ≃ₐ[F] L) := by
      rw [hram, h0]; simp
    have hnpos : (0 : ℝ) < (Nat.card (L ≃ₐ[F] L) : ℝ) := by
      exact_mod_cast Nat.card_pos

    obtain ⟨σ, hσ, hσB⟩ := GlobalTheory.T.exists_mem_upperRamificationGroup_jumpSum_not_mem' F L B h0 hB
    have hv : (0 : ℝ) ≤ (jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ) := by
      positivity

    obtain ⟨τ, hτ, hτC⟩ := GlobalTheory.T.exists_upper_mem_inv_mul_pow_mem_of_commutator F L p e _ C hcomm hv he σ hσ

    have hτ' : τ ∉ C := by
      intro hτmem
      apply hσB
      apply hpow
      have hsplit : σ ^ p = τ * (τ⁻¹ * σ ^ p) := by group
      rw [hsplit]
      exact C.mul_mem hτmem hτC
    have key := GlobalTheory.T.card_mul_le_jumpSum_of_mem_upperRamification_not_mem F L C _ h0 τ hτ hτ'
    have hR : ((min (2 * jumpSum (wild F L) ⊤ B) (jumpSum (wild F L) ⊤ B + E) : ℕ) : ℝ)
        ≤ (jumpSum (wild F L) ⊤ C : ℝ) := by
      refine le_trans (le_of_eq ?_) key
      rw [mul_min_of_nonneg _ _ hnpos.le, hEe, hcard]
      push_cast
      congr 1
      · field_simp
      · field_simp
    exact_mod_cast hR

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBreuilKisinHomUniformizerFrobeniusLe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem norm_toDisc_add_le_max (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (a b : A) :
    ‖toDisc l u ρ (a + b)‖ ≤ max ‖toDisc l u ρ a‖ ‖toDisc l u ρ b‖ := by
  have h1 : ∀ c, ‖toDisc l u ρ c‖ = gauge l u ρ (algebraMap A (PreDisc l u ρ) c) := fun c => norm_ofPre l u ρ _
  rewrite [h1, h1, h1, map_add]
  exact gauge_add_le_max l u ρ _ _

theorem norm_hf_g_X_and_φ_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ‖toDisc l (BK.hf f X) bk.ρ₀ (BK.hf g X)‖ ≤ bk.ρ₀ ∧ ‖toDisc l (BK.hf f X) bk.ρ₀ (B.D.φ (BK.hf f X))‖ ≤ bk.ρ₀ := by
  intro l _ K bk B f g
  obtain ⟨hρ0, hρ1, hlρ, hE⟩ := GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius l K bk B.A (BK.hf f)
  have hd := (GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f g).2.2
  have h : ‖toDisc l (BK.hf f X) bk.ρ₀ (BK.hf f X ^ 1)‖ ≤ (bk.ρ₀ : ℝ) ^ 1 := norm_toDisc_pow_le 1 hρ0
  have hX : ‖toDisc l (BK.hf f X) bk.ρ₀ (BK.hf f X)‖ ≤ bk.ρ₀ := by simpa only [pow_one] using h
  have key : ∀ a b : B.A, ‖toDisc l (BK.hf f X) bk.ρ₀ (a + b)‖ ≤
      max ‖toDisc l (BK.hf f X) bk.ρ₀ a‖ ‖toDisc l (BK.hf f X) bk.ρ₀ b‖ :=
    norm_toDisc_add_le_max l (BK.hf f X) bk.ρ₀
  refine ⟨?_, ?_⟩
  · obtain ⟨w, hw⟩ := hd
    have e : BK.hf g X = BK.hf f X + BK.hf f bk.E * w := eq_add_of_sub_eq' hw
    rewrite [e]
    refine (key _ _).trans (max_le hX ?_)
    rewrite [map_mul]
    refine (norm_mul_le _ _).trans ?_
    calc ‖toDisc l (BK.hf f X) bk.ρ₀ (BK.hf f bk.E)‖ * ‖toDisc l (BK.hf f X) bk.ρ₀ w‖
        ≤ (l : ℝ)⁻¹ * 1 := mul_le_mul hE (norm_toDisc_le w) (norm_nonneg _) (by positivity)
      _ ≤ bk.ρ₀ := (mul_one _).trans_le hlρ
  · have e1 : B.D.φ (BK.hf f X) = BK.hf f (frobS l bk.a X) :=
      (Hom.f_φ f (show bk.prism.A from X)).symm
    have e : B.D.φ (BK.hf f X) = BK.hf f X ^ l := by
      rw [e1, frobS_X, map_pow]
    refine (congrArg (fun y => ‖toDisc l (BK.hf f X) bk.ρ₀ y‖) e).trans_le ((norm_toDisc_pow_le l hρ0).trans ?_)
    exact pow_le_of_le_one (by positivity) (by exact_mod_cast hρ1.le) (Fact.out : l.Prime).ne_zero

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDiagTangentUnitFrameHolomorphicArcLeStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_diag_tangent_unitFrame_holomorphicArc_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∃ T B : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), GlobalTheory.FrameNorm.IsUnitFr (U.X k) x.1 → FrBor t (U.un k x) yw → ∀ j, ‖Formalism.L2.PjFree.toC (t (some j) : CAt σ)‖ ≤ B := by
  first | exact @GlobalTheory.ArcLieBound.norm_diag_le | exact GlobalTheory.ArcLieBound.norm_diag_le | (intros; apply GlobalTheory.ArcLieBound.norm_diag_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingNoZeroDivisorsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_ring_no_zero_divisors : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (x : AK K), x ≠ 0 → ∀ y : GlobalTheory.AcrisK.BK K,
    toB K (ofA K x) * y = 0 → y = 0 := by
  first | exact @GlobalTheory.AcrisNZD.main | exact GlobalTheory.AcrisNZD.main | (intros; apply GlobalTheory.AcrisNZD.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeDvdAinfEnvelopeOfGaloisSectionsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_dvd_ainfEnvelope_of_galois_sections : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (κ : Type) [Fintype κ] (x : κ → En.Q.A) (c : κ → κ → En.Q.A) (h : ℕ), (∀ j, En.inl.f (bk.ev bk.E) ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (s : Hom En.Q (ainfObj K)), s.comp En.inl = Hom.id _ → s.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ∣ s.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ∣ x j := by
  first | exact @GlobalTheory.BSP.l_dvd_of_galois_sections | exact GlobalTheory.BSP.l_dvd_of_galois_sections | (intros; apply GlobalTheory.BSP.l_dvd_of_galois_sections <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdIdeleCharacterEqOneOfTotallyPositiveStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_idele_character_eq_one_of_totallyPositive : ∀ (F : Type) [Field F] [NumberField F] (B : Type) [CommGroup B] (ψ : Neutral.B1.Ideles F →* B), IsOpen (ψ.ker : Set (Neutral.B1.Ideles F)) → (∀ k : Fˣ, ψ (Neutral.B1.diagUnits F k) = 1) → (∀ y ∈ GlobalTheory.HeckeGal.infConn F, ψ y = 1) → ∀ a : Fˣ, (∀ φ : F →+* ℝ, 0 < φ (a : F)) → ∀ T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), (∀ v ∉ T, ψ (GlobalTheory.NormCompat.locUnit F v a) = 1) → ∏ v ∈ T, ψ (GlobalTheory.NormCompat.locUnit F v a) = 1 := by
  first | exact @GlobalTheory.ProdLocUnitPos.prod_locUnit_eq_one_of_pos | exact GlobalTheory.ProdLocUnitPos.prod_locUnit_eq_one_of_pos | (intros; apply GlobalTheory.ProdLocUnitPos.prod_locUnit_eq_one_of_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientRowsExteriorDetEqConstMulTopBlockDet
section
open Matrix Formalism.IndefR.Datum GlobalTheory.ExportSeries

namespace GlobalTheory

theorem dU_eq_const_mul_det_topL_translate :
  ∀ (k : Type) [Field k] (r n : ℕ) (β : DetBases k r n) (U : Planes k r n),
  ∃ (g : GL (Fin n) k) (c : kˣ), ∀ y : Matrix (Fin r) (Fin n) k,
    dU β U y = (c : k) * (topL r (y * (g : Matrix (Fin n) (Fin n) k))).det := by
  intro k _ r n β U
  have hrn : r ≤ n := by have := U.2; omega
  let b := Module.finBasisOfFinrankEq k _ (finrank_quot U)
  have hU : Module.finrank k U.1 = n - r := by have := U.2; omega
  let bU := Module.finBasisOfFinrankEq k U.1 hU
  obtain ⟨lam, hlam⟩ := LinearMap.exists_extend (bU.equivFun.toLinearMap)
  let φ : (Fin n → k) →ₗ[k] (Fin n → k) := LinearMap.pi fun j =>
    if h : j.val < r then (LinearMap.proj (⟨j.val, h⟩ : Fin r)) ∘ₗ b.equivFun.toLinearMap ∘ₗ U.1.mkQ
    else (LinearMap.proj (⟨j.val - r, by have := j.2; omega⟩ : Fin (n - r))) ∘ₗ lam
  have hφ1 : ∀ v (i : Fin r), φ v ⟨i.val, by omega⟩ = b.repr (U.1.mkQ v) i := by
    intro v i
    simp [φ, i.2]
  have hφ2 : ∀ v (i : Fin (n - r)), φ v ⟨r + i.val, by omega⟩ = lam v i := by
    intro v i
    simp [φ]
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h1 : U.1.mkQ v = 0 := by
      apply b.repr.injective
      ext i
      have := hφ1 v i
      rw [hv] at this
      simpa using this.symm
    have hvU : v ∈ U.1 := by simpa using h1
    have h2 : bU.equivFun ⟨v, hvU⟩ = 0 := by
      have e : lam v = bU.equivFun ⟨v, hvU⟩ := by
        have := LinearMap.congr_fun hlam ⟨v, hvU⟩
        simpa using this
      rw [← e]
      ext i
      have := hφ2 v i
      rw [hv] at this
      simpa using this.symm
    have : (⟨v, hvU⟩ : U.1) = 0 := bU.equivFun.injective (by rw [h2, map_zero])
    simpa using congrArg Subtype.val this

  let ψ := LinearEquiv.ofInjectiveEndo φ hφ
  let A : Matrix (Fin n) (Fin n) k := (LinearMap.toMatrix' φ)ᵀ
  let B : Matrix (Fin n) (Fin n) k := (LinearMap.toMatrix' ψ.symm.toLinearMap)ᵀ
  have hAB : A * B = 1 := by
    have hc : ψ.symm.toLinearMap ∘ₗ φ = LinearMap.id := by
      refine LinearMap.ext fun v => ?_
      show ψ.symm (ψ v) = v
      exact ψ.symm_apply_apply v
    simp only [A, B, ← transpose_mul, ← LinearMap.toMatrix'_comp, hc, LinearMap.toMatrix'_id, transpose_one]
  have hBA : B * A = 1 := by
    have hc : φ ∘ₗ ψ.symm.toLinearMap = LinearMap.id := by
      refine LinearMap.ext fun v => ?_
      show ψ (ψ.symm v) = v
      exact ψ.apply_symm_apply v
    simp only [A, B, ← transpose_mul, ← LinearMap.toMatrix'_comp, hc, LinearMap.toMatrix'_id, transpose_one]
  let g : GL (Fin n) k := ⟨A, B, hAB, hBA⟩
  have hb : β.form U b ≠ 0 := fun h0 => β.ne U (by rw [(β.form U).eq_smul_basis_det b, h0, zero_smul])
  refine ⟨g, Units.mk0 _ hb, fun y => ?_⟩
  have key : ∀ i j, (y * A) i j = φ (y.row i) j := by
    intro i j
    rw [← congrFun (LinearMap.toMatrix'_mulVec φ (y.row i)) j]
    simp [A, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm, Matrix.row]
  have ht : topL r (y * (g : Matrix (Fin n) (Fin n) k)) = (b.toMatrix fun i => U.1.mkQ (y.row i))ᵀ := by
    ext i j
    have hj : j.val < n := by omega
    have e1 : topL r (y * (g : Matrix (Fin n) (Fin n) k)) i j = (y * A) i ⟨j.val, hj⟩ := by
      simp [topL, hj, g]
    rw [e1, key, hφ1 (y.row i) j, transpose_apply, Module.Basis.toMatrix_apply]
  rw [ht, det_transpose, ← Module.Basis.det_apply, dU]
  conv_lhs => rw [(β.form U).eq_smul_basis_det b]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecordCaseA
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Per.DdREqDcris

theorem record_caseA : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
    Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris ((D.loc l).PD K) ↥LL.1 := by
  intro D l _ K LL _ hb V _ _ _ _ _ ρ _ _ _ hc
  exact map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL hb V ρ hc

end GlobalTheory.Per.DdREqDcris
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerBoundOfAuxiliaryPrimesOddStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residualSelmerBound_of_auxiliaryPrimes_odd : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → GreenbergWiles → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ResidualBoundOddPrimes bkP := by
  first | exact @GlobalTheory.ResSel.residual_bound_of_parts | exact GlobalTheory.ResSel.residual_bound_of_parts | (intros; apply GlobalTheory.ResSel.residual_bound_of_parts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedCharIsCrystallineHodgeTateZeroStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedChar_isCrystalline_hodgeTate_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ), Continuous (fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → (∀ g ∈ IK K, μ g = 1) → IsCrys (P.PD K) (charRep μ) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = 0 then 1 else 0 := by
  first | exact @GlobalTheory.UnramifiedChar.isCrys_and_multV_eq | exact GlobalTheory.UnramifiedChar.isCrys_and_multV_eq | (intros; apply GlobalTheory.UnramifiedChar.isCrys_and_multV_eq <;> assumption)
end

