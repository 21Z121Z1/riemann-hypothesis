import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0048
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0059
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0046

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Pst.DpstMap

section Letter

variable {LL U D D' : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] [AddCommGroup D'] [Module LL D']
  (m : U →+* End LL D) (m' : U →+* End LL D') (F : Type) [Field F] [Algebra LL F] (τ : U →+* F)

def letterLin (T : D →ₗ[LL] D') (hT : ∀ c, T ∘ₗ m c = m' c ∘ₗ T) : Letter m F τ →ₗ[F] Letter m' F τ :=
  Submodule.mapQ _ _ (T.baseChange F) (iSup_le fun c => by
    rintro _ ⟨y, rfl⟩
    refine Submodule.mem_iSup_of_mem c ⟨T.baseChange F y, ?_⟩
    have := LinearMap.congr_fun (congrArg (LinearMap.baseChange F) (hT c)) y
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply] at this
    simp [this])

@[simp] theorem letterLin_mk (T : D →ₗ[LL] D') (hT : ∀ c, T ∘ₗ m c = m' c ∘ₗ T) (x : D) :
    letterLin m m' F τ T hT (letterMk m F τ x) = letterMk m' F τ (T x) := rfl

end Letter

section Dmap

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
  (ρ : Representation LL ↥(GK K) V) (ρ' : Representation LL ↥(GK K) V') (f : V →ₗ[LL] V')

def tensV : V ⊗[ℚ_[l]] Bst P →ₗ[LL] V' ⊗[ℚ_[l]] Bst P := AlgebraTensorModule.map f LinearMap.id

@[simp] theorem tensV_tmul (v : V) (b : Bst P) : tensV P f (v ⊗ₜ b) = f v ⊗ₜ b := rfl

theorem tensV_onB (T : End ℚ_[l] (Bst P)) (x : V ⊗[ℚ_[l]] Bst P) :
    tensV P f (onB P LL V T x) = onB P LL V' T (tensV P f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensV_stRep (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] Bst P) :
    tensV P f (stRep P ρ g x) = stRep P ρ' g (tensV P f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [hf]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {ρ ρ' f}

theorem tensV_mem_Dpst (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (x : V ⊗[ℚ_[l]] Bst P) (hx : x ∈ Dpst P ρ) :
    tensV P f x ∈ Dpst P ρ' := by
  obtain ⟨K', hK⟩ := (mem_Dpst P ρ).mp hx
  exact (mem_Dpst P ρ').mpr ⟨K', fun g hg => by rw [← tensV_stRep P ρ ρ' f hf, hK g hg]⟩

def dmap (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) : ↥(Dpst P ρ) →ₗ[LL] ↥(Dpst P ρ') :=
  (tensV P f).restrict (tensV_mem_Dpst P hf)

@[simp] theorem coe_dmap (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (x : ↥(Dpst P ρ)) :
    (dmap P hf x : V' ⊗[ℚ_[l]] Bst P) = tensV P f x := rfl

variable (hf : ∀ g v, f (ρ g v) = ρ' g (f v))
include hf

theorem dmap_phiD (x : ↥(Dpst P ρ)) : dmap P hf (phiD P ρ x) = phiD P ρ' (dmap P hf x) :=
  Subtype.ext (tensV_onB P f _ x.1)

theorem dmap_monD (x : ↥(Dpst P ρ)) : dmap P hf (monD P ρ x) = monD P ρ' (dmap P hf x) :=
  Subtype.ext (tensV_onB P f _ x.1)

theorem dmap_actD (g : ↥(GK K)) (x : ↥(Dpst P ρ)) : dmap P hf (actD P ρ g x) = actD P ρ' g (dmap P hf x) :=
  Subtype.ext (tensV_stRep P ρ ρ' f hf g x.1)

theorem dmap_mulD (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρ)) : dmap P hf (mulD P ρ c x) = mulD P ρ' c (dmap P hf x) :=
  Subtype.ext (tensV_onB P f _ x.1)

theorem dmap_phiU_zpow [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ')]
    (n : ℤ) (x : ↥(Dpst P ρ)) :
    dmap P hf (((phiU P ρ ^ n : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) x) =
      ((phiU P ρ' ^ n : (End LL ↥(Dpst P ρ'))ˣ) : End LL ↥(Dpst P ρ')) (dmap P hf x) := by
  have hinv : ∀ y, dmap P hf ((((phiU P ρ)⁻¹ : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) y) =
      (((phiU P ρ')⁻¹ : (End LL ↥(Dpst P ρ'))ˣ) : End LL ↥(Dpst P ρ')) (dmap P hf y) := by
    intro y
    have h1 : phiD P ρ' (dmap P hf ((((phiU P ρ)⁻¹ : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) y)) =
        dmap P hf y := by
      rw [← dmap_phiD, ← coe_phiU, ← End.mul_apply, Units.mul_inv]; rfl
    rw [← h1, ← coe_phiU, ← End.mul_apply, Units.inv_mul]; rfl
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, zpow_add_one, Units.val_mul, Units.val_mul, End.mul_apply, End.mul_apply, ih, coe_phiU,
      coe_phiU, dmap_phiD]
  | pred n ih =>
    rw [zpow_sub_one, zpow_sub_one, Units.val_mul, Units.val_mul, End.mul_apply, End.mul_apply, ih, hinv]

end Dmap

section Lin

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {K LL : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
  [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V']
  {ρ : Representation ↥LL.1 ↥(GK K) V} {ρ' : Representation ↥LL.1 ↥(GK K) V'} {f : V →ₗ[↥LL.1] V'}
  (hf : ∀ g v, f (ρ g v) = ρ' g (f v))

def wdLin : WDSpace P ι ρ →ₗ[ℂ] WDSpace P ι ρ' :=
  letI := algC ι LL
  letterLin (mulD P ρ) (mulD P ρ') ℂ (urC ι) (dmap P hf) fun c => LinearMap.ext fun x => dmap_mulD P hf c x

@[simp] theorem wdLin_mk (x : ↥(Dpst P ρ)) : wdLin P ι hf (wdMk P ι ρ x) = wdMk P ι ρ' (dmap P hf x) := rfl

theorem wdLin_wdN (y : WDSpace P ι ρ) : wdLin P ι hf (wdN P ι ρ y) = wdN P ι ρ' (wdLin P ι hf y) := by
  have : (wdLin P ι hf).comp (wdN P ι ρ) = (wdN P ι ρ').comp (wdLin P ι hf) :=
    LinearMap.ext_on_range (span_wdMk P ι ρ) fun x => by
      simp only [LinearMap.comp_apply, wdN_mk, wdLin_mk, dmap_monD]
  exact LinearMap.congr_fun this y

end Lin

section Weil

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
  {LL : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
  [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V']
  {ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V} {ρ' : Representation ↥LL.1 ↥(GK Bw.Kw) V'} {f : V →ₗ[↥LL.1] V'}
  (hf : ∀ g v, f (ρ g v) = ρ' g (f v))
  [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ')]

theorem dmap_weilD (σ : ↥(Weil h)) (x : ↥(Dpst P ρ)) :
    dmap P hf (weilD Bw h P ρ σ x) = weilD Bw h P ρ' σ (dmap P hf x) := by
  rw [weilD_apply, weilD_apply]
  exact (dmap_actD P hf _ _).trans (congrArg _ (dmap_phiU_zpow P hf _ x))

theorem wdLin_wdRho (σ : ↥(Weil h)) (y : WDSpace P ι ρ) :
    wdLin P ι hf (wdRho P ι Bw h hj ρ σ y) = wdRho P ι Bw h hj ρ' σ (wdLin P ι hf y) := by
  have : (wdLin P ι hf).comp (wdRho P ι Bw h hj ρ σ) = (wdRho P ι Bw h hj ρ' σ).comp (wdLin P ι hf) :=
    LinearMap.ext_on_range (span_wdMk P ι ρ) fun x => by
      simp only [LinearMap.comp_apply, wdRho_mk, wdLin_mk, dmap_weilD]
  exact LinearMap.congr_fun this y

end Weil

section Charpoly

theorem charpoly_dvd_of_surjective {K M M' : Type} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [AddCommGroup M'] [Module K M'] [FiniteDimensional K M'] (F : M →ₗ[K] M') (hF : Function.Surjective F)
    (T : Module.End K M) (T' : Module.End K M') (hT : ∀ x, F (T x) = T' (F x)) :
    T'.charpoly ∣ T.charpoly := by
  have hA : ∀ x ∈ LinearMap.ker F, T x ∈ LinearMap.ker F := fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢; rw [hT, hx, map_zero]
  rw [GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ (LinearMap.ker F) T hA]
  refine Dvd.intro_left (T.restrict hA).charpoly ?_
  let e := F.quotKerEquivOfSurjective hF
  have he : (LinearMap.ker F).mapQ (LinearMap.ker F) T (fun x hx => hA x hx) = e.symm.conj T' := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.symm_symm]
    apply e.injective
    rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
    simp only [e, LinearMap.quotKerEquivOfSurjective_apply_mk, hT]
    rfl
  rw [he, LinearEquiv.charpoly_conj]

theorem isNilpotent_zpow_sub_one {R : Type} [Ring R] (u : Rˣ) (hu : IsNilpotent ((u : R) - 1)) (n : ℤ) :
    IsNilpotent (((u ^ n : Rˣ) : R) - 1) := by
  have hnat : ∀ k : ℕ, IsNilpotent ((u : R) ^ k - 1) := fun k => by
    rw [← geom_sum_mul]
    refine Commute.isNilpotent_mul_left ?_ hu
    exact Commute.sum_left _ _ _ fun i _ =>
      ((Commute.refl (u : R)).sub_right (Commute.one_right _)).pow_left i
  rcases n with k | k
  · rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
    exact hnat k
  · rw [zpow_negSucc]
    have e : (((u ^ (k + 1))⁻¹ : Rˣ) : R) - 1 = (((u ^ (k + 1))⁻¹ : Rˣ) : R) * -(((u : R) ^ (k + 1)) - 1) := by
      rw [mul_neg, mul_sub, mul_one, ← Units.val_pow_eq_pow_val, Units.inv_mul]; abel
    rw [e]
    refine Commute.isNilpotent_mul_left ?_ (hnat (k + 1)).neg
    refine Commute.neg_right ?_
    rw [← Units.val_pow_eq_pow_val]
    exact (Commute.units_inv_left (Commute.refl _)).sub_right (Commute.one_right _)

theorem commute_isNilpotent_of_unipotent {R : Type} [Ring R] {a b : R} (u : Rˣ) (hu : IsNilpotent ((u : R) - 1))
    (n : ℤ) (hc : Commute (u : R) b) (hb : b = a * ((u ^ n : Rˣ) : R)) : Commute a b ∧ IsNilpotent (b - a) := by
  have hUb : Commute ((u ^ n : Rˣ) : R) b := hc.units_zpow_left n
  have ha : a = b * (((u ^ n)⁻¹ : Rˣ) : R) := by rw [hb, mul_assoc, Units.mul_inv, mul_one]
  have haU : Commute a ((u ^ n : Rˣ) : R) := by
    rw [ha]
    exact hUb.symm.mul_left (Commute.units_inv_left (Commute.refl _))
  refine ⟨?_, ?_⟩
  · rw [hb]; exact (Commute.refl a).mul_right haU
  · have e : b - a = a * (((u ^ n : Rˣ) : R) - 1) := by rw [hb, mul_sub, mul_one]
    rw [e]
    exact Commute.isNilpotent_mul_left (haU.sub_right (Commute.one_right _)) (isNilpotent_zpow_sub_one u hu n)

end Charpoly

section Semisimple

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
  {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
  (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]

theorem charpoly_wdRep (σ : ↥(Weil h)) :
    ((wdRep P ι Bw h hj ρ).ρ σ).charpoly = (wdRho P ι Bw h hj ρ σ).charpoly := by
  obtain ⟨u, -, hu, -, hcomm, hρ⟩ := wdRep_spec P ι Bw h hj ρ
  obtain ⟨h1, h2⟩ := commute_isNilpotent_of_unipotent u hu (deg σ) (hcomm σ) (hρ σ)
  exact GlobalTheory.WeilDeligne.charpoly_eq_of_isNilpotent_sub h1 h2

theorem charPol_wdPst [FiniteDimensional ↥LL.1 V] (hV : IsPst P ρ) (σ : ↥(Weil h)) :
    WD.charPol (wdPst P ι Bw h hj ρ) σ = (wdRho P ι Bw h hj ρ σ).charpoly := by
  rw [wdPst_of_isPst ι Bw h hj hV, WD.charPol_mk, charpoly_wdRep]

end Semisimple

end GlobalTheory.Pst.DpstMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElevenLeInertOddPrimeImagQuadraticLargeScale
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.InertPrimeEleven

theorem eleven_le : ∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (l : ℕ),
    L.sc.ez = eps → x0 ≤ L.sc.x → l.Prime → InertUnr D l → 11 ≤ l := by
  intro eps heps
  refine ⟨(11 : ℝ) ^ (5 / eps), ?_⟩
  intro D L l he hx hl hin
  have hlt := GlobalTheory.InertPrimeLarge.lt_prime L l hl hin.ne_two hin.2.2.2
  rw [he] at hlt
  have h0 : (0 : ℝ) ≤ (11 : ℝ) ^ (5 / eps) := Real.rpow_nonneg (by norm_num) _
  have hmono : ((11 : ℝ) ^ (5 / eps)) ^ (eps / 5) ≤ L.sc.x ^ (eps / 5) :=
    Real.rpow_le_rpow h0 hx (by positivity)
  have h11 : ((11 : ℝ) ^ (5 / eps)) ^ (eps / 5) = 11 := by
    rw [← Real.rpow_mul (by norm_num)]
    have : 5 / eps * (eps / 5) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have : (11 : ℝ) < l := by linarith
  exact_mod_cast this.le

end GlobalTheory.InertPrimeEleven
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBaseReads
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem exists_base_reads : ∀ {R : Ranks} (H : Host R) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (c : H.E →+* ↥K.1) (ι : Om l ≃+* ℂ) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (g₀ : R.GG), ι.toRingHom.comp (LL.1.val.toRingHom.comp (τ₀.toRingHom.comp c)) = H.emb g₀ → ∃ κ : H.E →+* ↥LL.1, ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (g : R.GG), ι.toRingHom.comp (LL.1.val.toRingHom.comp (τ.toRingHom.comp c)) = H.emb g → Reads H c κ τ g := by
  intro R H l _ K LL c ι τ₀ g₀ h₀
  refine ⟨τ₀.toRingHom.comp (c.comp ((H.sigmaOf g₀).symm : H.E →+* H.E)), ?_⟩
  intro τ g hτ x
  have hinj : Function.Injective (fun y : ↥LL.1 => ι (LL.1.val y)) :=
    ι.injective.comp (LL.1.val.injective)
  apply hinj
  have e1 := DFunLike.congr_fun hτ x
  have e2 := DFunLike.congr_fun h₀ ((H.sigmaOf g₀).symm (H.sigmaOf g x))
  simp only [RingHom.comp_apply] at e1 e2
  simp only [RingHom.comp_apply]
  change ι (LL.1.val (τ (c x))) = ι (LL.1.val (τ₀ (c ((H.sigmaOf g₀).symm (H.sigmaOf g x)))))
  have e1' : ι (LL.1.val (τ (c x))) = H.emb g x := e1
  have e2' : ι (LL.1.val (τ₀ (c ((H.sigmaOf g₀).symm (H.sigmaOf g x))))) = H.emb g₀ ((H.sigmaOf g₀).symm (H.sigmaOf g x)) := e2
  rw [e1', e2']
  simp [Host.emb]

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDecorationExtensionAtPrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.FrameDeco

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

omit [StarRing E] in

theorem exists_inv_mod (P : HeightOneSpectrum (𝓞 E)) {s : 𝓞 E} (hs : s ∉ P.asIdeal) :
    ∃ a p : 𝓞 E, p ∈ P.asIdeal ∧ a * s + p = 1 := by
  obtain ⟨a, p, hp, h⟩ := P.isMaximal.exists_inv hs
  exact ⟨a, p, hp, h⟩

theorem smul_localizationAt_le (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) :
    P.asIdeal • localization₂ P.asIdeal N ≤ localization₂ P.asIdeal (P.asIdeal • N) := by
  rw [Submodule.smul_le]
  intro r hr x hx
  obtain ⟨t, ht, htx⟩ := (mem_locP P N x).1 hx
  refine (mem_locP P _ _).2 ⟨t, ht, ?_⟩
  rw [smul_comm]
  exact Submodule.smul_mem_smul hr htx

theorem mem_smul_of_mem_locP (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n))
    {y : Sp E n} (hy : y ∈ N) (h : y ∈ localization₂ P.asIdeal (P.asIdeal • N)) : y ∈ P.asIdeal • N := by
  obtain ⟨t, ht, hty⟩ := (mem_locP P _ _).1 h
  obtain ⟨a, p, hp, e⟩ := exists_inv_mod P ht
  have : y = a • (t • y) + p • y := by
    rw [smul_smul, ← add_smul, e, one_smul]
  rw [this]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hty) (Submodule.smul_mem_smul hp hy)

theorem redV_add (P : HeightOneSpectrum (𝓞 E)) {x y : Sp E n}
    (hx : x ∈ stdAt E n P) (hy : y ∈ stdAt E n P) : redV P (x + y) = redV P x + redV P y := by
  funext i
  exact reduction_add ((mem_localization_standardLattice _ _).1 hx _) ((mem_localization_standardLattice _ _).1 hy _)

theorem redV_osmul (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E) {x : Sp E n}
    (hx : x ∈ stdAt E n P) :
    redV P (a • x) = Ideal.Quotient.mk P.asIdeal a • redV P x := by
  funext i
  exact redP_osmul a ((mem_localization_standardLattice _ _).1 hx _)

theorem exists_deco_of_frames : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (d : DecoSet E n ST ∅) (f : SG → (Sp E n ≃ₗ[E] Sp E n)), (∀ (w : SG) (x : Sp E n), f w x ∈ d.1.at w.1 ↔ x ∈ stdAt E n w.1) → ∃ d' : DecoSet E n ST SG, d'.1.N = d.1.N ∧ d'.1.f = d.1.f ∧ ∀ w : SG, ∀ x ∈ stdAt E n w.1, d'.1.be w (f w x) = redV w.1 x := by
  classical
  intro E _ _ _ n ST SG d f hf
  have hf' : ∀ (w : SG) (y : Sp E n), y ∈ d.1.at w.1 → (f w).symm y ∈ stdAt E n w.1 := by
    intro w y hy
    exact (hf w _).1 (by simpa using hy)
  let D : Deco E n ST SG :=
    { N := d.1.N
      f := d.1.f
      be := fun w y => if y ∈ d.1.at w.1 then redV w.1 ((f w).symm y) else 0 }
  have hbe : ∀ (w : SG) (y : Sp E n), y ∈ d.1.at w.1 → D.be w y = redV w.1 ((f w).symm y) :=
    fun w y hy => if_pos hy
  have hsm : ∀ (w : SG) (a : 𝓞 E), ∀ x ∈ d.1.at w.1,
      D.be w (a • x) = Ideal.Quotient.mk w.1.asIdeal a • D.be w x := by
    intro w a x hx
    rw [hbe w _ (Submodule.smul_mem _ a hx), hbe w _ hx, equiv_osmul, redV_osmul _ _ (hf' w x hx)]
  have hD : D.Ok :=
    { lat := d.2.lat
      uni := d.2.uni
      f_add := d.2.f_add
      f_smul := d.2.f_smul
      f_off := d.2.f_off
      f_ne := d.2.f_ne
      be_add := by
        intro w x hx y hy
        replace hx : x ∈ d.1.at w.1 := hx
        replace hy : y ∈ d.1.at w.1 := hy
        rw [hbe w _ (Submodule.add_mem _ hx hy), hbe w _ hx, hbe w _ hy, map_add,
          redV_add _ (hf' w x hx) (hf' w y hy)]
      be_smul := hsm
      be_off := fun w x hx => if_neg hx
      be_surj := by
        intro w c
        choose r hr using fun i => Ideal.Quotient.mk_surjective (c i)
        have h1 : (fun i => algebraMap (𝓞 E) E (r i) : Sp E n) ∈ stdLat E n :=
          (mem_stdLat _).2 fun i => ⟨r i, rfl⟩
        have h2 := (hf w _).2 (le_locP _ _ h1)
        obtain ⟨s, hs, hsy⟩ := (mem_locP _ _ _).1 h2
        obtain ⟨a, p, hp, e⟩ := exists_inv_mod w.1 hs
        refine ⟨a • s • _, Submodule.smul_mem _ a hsy, ?_⟩
        have e' : Ideal.Quotient.mk w.1.asIdeal (a * s) = 1 := by
          have := congrArg (Ideal.Quotient.mk w.1.asIdeal) e
          rwa [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hp, add_zero, map_one] at this
        rw [smul_smul, hsm w _ _ h2, e', one_smul, hbe w _ h2, LinearEquiv.symm_apply_apply]
        funext i
        exact (reduction_coe _ _).trans (hr i)
      be_ker := by
        intro w y hy h0
        replace hy : y ∈ d.1.N := hy
        have hy' : y ∈ d.1.at w.1 := le_locP _ _ hy
        rw [hbe w _ hy'] at h0
        have hx := hf' w y hy'
        obtain ⟨s, hs, hsx⟩ := (mem_locP _ _ _).1 hx
        have h0' : redV w.1 (s • (f w).symm y) = 0 := by
          rw [redV_osmul _ _ hx, h0, smul_zero]
        choose r hr using (mem_stdLat _).1 hsx
        have hmem : ∀ i, r i ∈ w.1.asIdeal := by
          intro i
          have h3 : redP w.1 ((s • (f w).symm y) i) = 0 := congrFun h0' i
          rw [← hr i, reduction_coe] at h3
          exact Ideal.Quotient.eq_zero_iff_mem.1 h3
        have h4 : s • (f w).symm y
            = ∑ i, r i • (Pi.single i (algebraMap (𝓞 E) E 1) : Sp E n) := by
          generalize s • (f w).symm y = x at hr
          funext j
          simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]
        have h5 : s • y ∈ w.1.asIdeal • d.1.at w.1 := by
          have : s • y = f w (s • (f w).symm y) := by
            rw [equiv_osmul, LinearEquiv.apply_symm_apply]
          rw [this, h4, map_sum]
          refine Submodule.sum_mem _ fun i _ => ?_
          rw [equiv_osmul]
          exact Submodule.smul_mem_smul (hmem i)
            ((hf w _).2 (le_locP _ _ (single_mem_stdLat i 1)))
        obtain ⟨t, ht, hts⟩ := (mem_locP _ _ _).1 (smul_localizationAt_le w.1 d.1.N h5)
        refine mem_smul_of_mem_locP w.1 d.1.N hy ((mem_locP _ _ _).2 ⟨t * s, ?_, ?_⟩)
        · exact fun hm => (w.1.isPrime.mem_or_mem hm).elim ht hs
        · rwa [mul_smul] }
  refine ⟨⟨D, hD⟩, rfl, rfl, fun w x hx => ?_⟩
  change D.be w (f w x) = _
  rw [hbe w _ ((hf w x).2 hx), LinearEquiv.symm_apply_apply]

end GlobalTheory.FrameDeco
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTypePrimeUnderEqStatement
section
open NumberField IsDedekindDomain Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_typePrime_under_eq : ∀ (X : Fields) (Pr : Primes X), X.Ok → Pr.Ok → ∀ (i : Fin 2) (P : HeightOneSpectrum (𝓞 X.E)), ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal → ∃ P' ∈ Pr.vG i, P'.under (𝓞 X.F) = P.under (𝓞 X.F) := by
  first | exact @GlobalTheory.GprimUnder.exists_vG_under | exact GlobalTheory.GprimUnder.exists_vG_under | (intros; apply GlobalTheory.GprimUnder.exists_vG_under <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingReadsGaloisElement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem existsUnique_reads : ∀ {R : Ranks} (H : Host R) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (c : H.E →+* ↥K.1) (κ : H.E →+* ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1), ∃! g : R.GG, Reads H c κ τ g := by
  intro R H l _ K LL c κ τ
  haveI : IsGalois ℚ H.E := H.hostE_isGalois
  obtain ⟨σ, hσ⟩ := GlobalTheory.HTW.exists_aut_comp_eq_of_normal κ ((τ : ↥K.1 →+* ↥LL.1).comp c)
  obtain ⟨g, hg⟩ := (H.gal).symm.surjective σ
  have hg' : H.sigmaOf g = σ := hg
  refine ⟨g, fun x => ?_, fun g' hg2 => ?_⟩
  · rw [hg']
    exact hσ x
  · have e : H.sigmaOf g' = H.sigmaOf g := by
      refine AlgEquiv.ext fun x => ?_
      apply κ.injective
      rw [← hg2 x, hg']
      exact hσ x
    exact (H.gal).symm.injective e

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingRestrictsToWachLetterUnrami
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem existsUnique_over : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL),
    K.1 ≤ MaximalUnramifiedExtension l → ∀ a, ∃! τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Over W τ a := by
  intro l _ P K LL W hK a
  have hle : K.1 ≤ K0 K := le_inf le_rfl hK
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) := by
    intro x
    exact ⟨⟨x.1, hle x.2⟩, Subtype.ext rfl⟩
  let e : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥K.1 :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)
      ⟨(IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1).toRingHom.injective, hsurj⟩
  refine ⟨(W.emb a).comp e.symm.toAlgHom, ?_, ?_⟩
  · show ((W.emb a).comp e.symm.toAlgHom).comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb a
    ext x
    have : e.symm ((IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) x) = x := e.symm_apply_apply x
    simp only [AlgHom.comp_apply]
    exact congrArg (fun z => ((W.emb a z : ↥LL.1) : Om l)) this
  · intro τ hτ
    have hτ' : τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb a := hτ
    ext x
    obtain ⟨y, rfl⟩ := hsurj x
    have h1 : e.symm ((IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) y) = y := e.symm_apply_apply y
    have h2 := congrArg (fun f => f y) hτ'
    simp only [AlgHom.comp_apply] at h2 ⊢
    rw [h2]
    exact congrArg (fun z => ((W.emb a z : ↥LL.1) : Om l)) h1.symm

end GlobalTheory.HTW.Rec
end

