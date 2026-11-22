import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftDarbouxAdelicSymplectic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0502
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1594
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1499
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1144
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1584
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarPullbackHolomorphicZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzGenuineUnitaryRepSignatures
section
noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD GlobalTheory.RealWeil GlobalTheory.ArchUniq GlobalTheory.ArchRep

namespace GlobalTheory.ArchRepD

theorem archRepD :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ →
    ∃ (ρ : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ u : Matrix α β (AE F E), At (evI F) u → ∀ f f₁ : SInf F κ,
          (∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h) →
            ∀ h : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F (ρ g f) h) = pureA F (ρ g f₁) h) ∧
        ∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
          ∫ x, star (ρ g f₁ x) * ρ g f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) ∧
      (∀ (L : SInf F κ →L[ℂ] ℂ) (f : SInf F κ),
        ContinuousOn (fun g => L (ρ g f)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ∀ γ ∈ RLines σ JB, ∀ Y, IsGenD τ C γ Y → ∀ (T : TensD F P Q R S) (L : SInf F κ →L[ℂ] ℂ),
        HasDerivAt (fun t : ℝ => L (ρ (γ (Multiplicative.ofAdd t)) (Φ T)))
          (L (Φ (sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) + (c₀ w * (Y w).trace) • 1) T))) 0 := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨n, θ, φ, φ₀, hp, hq, hφ, hφu⟩ := GlobalTheory.T.exists_archimedean_phaseSpace_coordinates_placeSignatures F E σ α β κ P Q R S τ JA JB d a b A C hCM hFr
  obtain ⟨k, hkc, hkC, hkJ, hcan⟩ := GlobalTheory.T.exists_continuous_hom_unitary_realPlaces_placewise_signature F E σ β R S τ JB b C hCM hFr.2.2
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨ω, hωc, hωi⟩ := GlobalTheory.T.exists_oscillator_action_normalising_schrodinger _ _ P Q R S φ hφ (GlobalTheory.T.continuous_rho_apply _) (UG (cA σ) JB) k hkc hkJ
  obtain ⟨s, hsc, hsφ⟩ := GlobalTheory.T.exists_symplectic_hom_of_unitary_transpose_action _ _ P Q R S φ hφ (UG (cA σ) JB) k hkc hkJ
  obtain ⟨ρ, η, hη1, hη2, hη3, hρi, hρu, hρc, hρd⟩ :=
    realRep GlobalTheory.Published.realMetaplecticRepresentation_holds s hsc ω hωc fun g w v => by
      obtain ⟨c, rfl⟩ := φ.surjective w
      rw [hsφ, hωi]
  obtain ⟨kk, hkk⟩ := GlobalTheory.T.deriv_continuous_character_real_unitary_one_parameter F E σ β R S τ JB b C hCM hFr.2.2 η (fun g h _ _ => hη1 g h) hη2.continuousOn
    fun g _ => hη3 g
  let toE : SInf F κ →L[ℂ] Sch (Fin n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) θ.symm
  let toV : Sch (Fin n) →L[ℂ] SInf F κ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) θ
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑θ.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑θ := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  have hEV : ∀ h, toE (toV h) = h := fun h => by ext x; simp [htoE, htoV]
  clear_value toE toV
  have hS := SchrTransport.schr_coords (trP F κ) θ φ₀ hp hq
  let ρ' : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ) :=
    { toFun := fun g => toV ∘L ρ g ∘L toE
      map_one' := ContinuousLinearMap.ext fun f => by
        rw [map_one]
        exact hVE f
      map_mul' := fun g h => ContinuousLinearMap.ext fun f => by
        simp only [map_mul, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, hEV] }
  have hρ' : ∀ g f, ρ' g f = toV (ρ g (toE f)) := fun _ _ => rfl
  clear_value ρ'
  refine ⟨ρ', fun w => kk w / 2, fun g _ => ⟨fun u hu f f₁ hf h => ?_, fun ν hν f₁ f₂ => ?_⟩, fun L f => ?_,
    fun γ hγ Y hY T L => ?_⟩
  · choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    obtain ⟨c, hc⟩ : ∃ c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ,
        ∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ :=
      ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, fun w => by
        have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
        simp only [Matrix.mul_assoc]
        rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    have hu' : At (evI F) (actB (cA σ) g u) := fun t ht => by
      rw [actB, ← Matrix.smul_mul, hu t ht, Matrix.zero_mul]
    have hc' : ∀ w, (actB (cA σ) g u).map (piInf (τ w)) = A w * (c w * (k g w)ᵀ) * (C w)ᵀ := fun w => by
      rw [actB, Matrix.map_mul, hc, Matrix.transpose_map, Matrix.mul_assoc, ← Matrix.transpose_mul, hkC,
        Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    have e1 : ⇑f₁ = schrF (trP F κ) (locV (d.e u).1, locV (d.e u).2) ⇑f := by
      funext y
      have := congrFun ((GlobalTheory.T.heisenbergOp_archimedean_vector_acts_by_schrodinger_trace F E σ α β κ ψ JA JB d hψ u hu f fun _ => 1).symm.trans (hf fun _ => 1)) (liftV y)
      simpa [pureA, liftV] using this.symm
    have e2 : ⇑(toE f₁) = rhoFun (φ c) ⇑(toE f) := by
      have := hS (locV (d.e u).1, locV (d.e u).2) ⇑(toE f)
      rw [← htoV, hVE, ← e1, ← hφu u c hu hc] at this
      rw [htoE, this]
      funext x
      simp
    have e3 := hρi g _ _ _ e2
    rw [hsφ, hφu _ _ hu' hc'] at e3
    rw [GlobalTheory.T.heisenbergOp_archimedean_vector_acts_by_schrodinger_trace F E σ α β κ ψ JA JB d hψ _ hu', hρ', hρ', htoV, htoV, hS, e3]
  · haveI : BorelSpace ({w : InfinitePlace F // w.IsReal} → ℝ) := Pi.borelSpace
    haveI : BorelSpace ({w : InfinitePlace F // w.IsComplex} → ℂ) := Pi.borelSpace
    haveI : BorelSpace (mixedEmbedding.mixedSpace F) := Prod.borelSpace
    haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := Pi.borelSpace
    obtain ⟨r, hr⟩ := haar_coords ν θ
    rw [hr, hr]
    congr 1
    simp only [hρ', htoV, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    rw [hρu]
    simp only [htoE, Function.comp_apply]
  · simp only [hρ']
    exact (hρc (L ∘L toV) (toE f)).continuousOn
  · have hkY : ∀ (t : ℝ) w, k (γ (Multiplicative.ofAdd t)) w = NormedSpace.exp (t • Y w) := fun t w =>
      hcan w _ _ ((hkC _ w).symm.trans (hY t w))
    have hYu : ∀ w, Y w ∈ upq (R w) (S w) := fun w => GlobalTheory.RealLiftGen.mem_upq_of (Y w) fun t => by
      have := congrArg (fun X => X.map star) (hkJ (γ (Multiplicative.ofAdd t)) w)
      simp only [GlobalTheory.RealLiftGen.map_star_mul, GlobalTheory.RealLiftGen.Jm_map_star, hkY] at this
      refine Eq.trans ?_ this
      congr 2
      ext i j
      simp
    obtain ⟨Z, hZ, hZφ, hZe⟩ := GlobalTheory.T.exists_symplecticLie_right_action_realCoordinates _ _ P Q R S φ hφ Y hYu
    have hsZ : ∀ t : ℝ, (s (γ (Multiplicative.ofAdd t)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) =
        NormedSpace.exp (t • Z) := fun t => Matrix.toLin'.injective (LinearMap.ext fun v => by
      obtain ⟨c, rfl⟩ := φ.surjective v
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hsφ, hZe]
      simp only [hkY])
    have hd := hρd (fun t => γ (Multiplicative.ofAdd t)) (hγ.1.comp continuous_ofAdd) (by simp) Z hZ hsZ _
      (hkk γ hγ Y hY) (L ∘L toV) (toE (Φ T))
    obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ α β κ ψ JA JB d hψ
    have hΨ : ∀ c T, (toE.toLinearMap ∘ₗ Φ) (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) ((toE.toLinearMap ∘ₗ Φ) T) := by
      intro c T
      obtain ⟨u, ⟨hu, hc⟩, -⟩ := GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM fun w => A w * c w * (C w)ᵀ
      have e1 := (GlobalTheory.RealLift.actsLaws F κ (Φ T) _ _).2.2.2.2 _ (hΦ.2 u hu c hc T) (hD u hu (Φ T)).1
      ext x
      obtain ⟨y, rfl⟩ := θ.surjective x
      have e2 := SchrTransport.dRho_coords (trP F κ) θ φ₀ hp hq (locV (d.e u).1, locV (d.e u).2) (Φ T) (toE (Φ T))
        (by rw [← htoV, hVE]) y
      rw [← hφu u c hu hc] at e2
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [← e2, e1, htoE, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
      exact (hD u hu (Φ T)).2 y
    have e3 := GlobalTheory.T.fockAction_quadraticOperators_factorSignatures _ _ P Q R S φ hφ _ hΨ Y hYu Z hZφ T
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at e3
    simp only [hρ']
    refine hd.congr_deriv ?_
    rw [e3, sumPl_add_smul]
    simp only [ContinuousLinearMap.comp_apply, hVE, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_add, map_smul, smul_eq_mul, Finset.sum_div]
    congr 2
    exact Finset.sum_congr rfl fun w _ => by ring

end GlobalTheory.ArchRepD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsIdealSpMapClosedPoint
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.Vanishing.H0 GlobalTheory.HermTools GlobalTheory.HilbertSamuel
open GlobalTheory.AllWt (Psi secZ exOf wtOf cuspOn latOn normOn petOn GoodOn suppOn LiesOn LiesOff)
open GlobalTheory.FlagMod (FlagCover FlagModel Frames frX ev)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open GlobalTheory.CompHt (hodgeWt uPrime genVal)

open GlobalTheory.Adelic (ptOf le_iff_ptOf_mem ptOf_comp resPt ptOf_resPt valR_ne_zero_iff LinSys)
open GlobalTheory.FlatLine (idem evR_idem idem_mem_suppOn)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Generic

variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)

theorem asIdeal_spMap_closedPoint {A K : Type} [CommRing A] [Field K] (φ : A →+* K) :
    ((spMap φ (IsLocalRing.closedPoint K) : Sp A) : PrimeSpectrum A).asIdeal = RingHom.ker φ := by
  show Ideal.comap φ (IsLocalRing.maximalIdeal K) = _
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

theorem specializes_ptY_genFr (h : GenFrEx Xo c) {L : Type} [Field L] [Algebra c.F L] (Q : FrPt Xo c L)
    (hQ : LiesOn Z Q) : ptOf (X.ptY (genFr h Z)) ⤳ ptOf (X.ptY Q) := by
  obtain ⟨C, ψ, z, t', hz, hb⟩ := (Reg.evLaws_genFr_atlas E H Dw l Xo c).2.2.2 h L Q
  have hsp : ptOf (X.ptY (genFr h C.Z)) ⤳ ptOf (X.ptY Q) := by
    rw [X.ptY_frBor C.bor, ← X.ptY_frMap C.gen, ← X.ptY_frBor hb, ← X.ptY_frMap hz, ptOf_comp, ptOf_comp]
    refine Specializes.map ?_ (X.ptY C.y).continuous
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    show ((spMap _ (IsLocalRing.closedPoint _) : Sp C.R) : PrimeSpectrum C.R).asIdeal ≤
      ((spMap _ (IsLocalRing.closedPoint _) : Sp C.R) : PrimeSpectrum C.R).asIdeal
    rw [asIdeal_spMap_closedPoint, asIdeal_spMap_closedPoint]
    refine le_of_eq_of_le ((RingHom.injective_iff_ker_eq_bot _).1 ?_) bot_le
    exact Subtype.val_injective
  have hZ : C.Z = Z := by
    have h1 : ptOf (X.ptY Q) ∈ X.π ⁻¹ᵁ barComp Y Z := (le_iff_ptOf_mem _ _).1 ((ptY_le_iff X Z Q).2 hQ)
    have h2 := hsp.mem_open (Opens.isOpen _) h1
    have hl : LiesOn Z (genFr h C.Z) := (ptY_le_iff X Z _).1 ((le_iff_ptOf_mem _ _).2 h2)
    by_contra hne
    have h3 := GlobalTheory.AllWt.evC_eq_zero h hne (idem_mem_suppOn Z)
    rw [evC, evR_idem hl (GlobalTheory.FlagTan.fromTest_of_isLocalRing _)] at h3
    exact one_ne_zero h3
  exact hZ ▸ hsp

variable {X Z} (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))

theorem exists_lift_genFr (h : GenFrEx Xo c) :
    ∃ z : Sp (Om Z) ⟶ M.X, z ≫ toFlag M = X.ptY (genFr h Z) ∧ ⊤ ≤ z ⁻¹ᵁ M.off := by
  have h1 : ⊤ ≤ X.ptY (genFr h Z) ⁻¹ᵁ (X.π ⁻¹ᵁ barComp Y Z) := (ptY_le_iff X Z _).2 (GlobalTheory.AllWt.liesOn_genFr h Z)
  have hr : Set.range (X.ptY (genFr h Z)) ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩; exact ⟨⟨_, h1 (Set.mem_univ s)⟩, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w ≫ inc₀ X Z = X.ptY (genFr h Z) := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have hU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z := fun s _ => by
    show (w ≫ inc₀ X Z) s ∈ flagOpen X
    rw [hw, ← X.pt_inc]
    exact (top_le_inc X) (Set.mem_univ _)
  obtain ⟨z, hz, -⟩ := M.existsUnique_lift w hU
  refine ⟨z, by rw [toFlag, ← Category.assoc, hz, hw], fun s _ => ?_⟩
  rw [M.off_eq]
  show (z ≫ M.σ) s ∈ U₀ X Z
  rw [hz]
  exact hU (Set.mem_univ s)

theorem isGenericPoint_of_lift (h : GenFrEx Xo c) {z : Sp (Om Z) ⟶ M.X} (hz : z ≫ toFlag M = X.ptY (genFr h Z))
    (hO : ⊤ ≤ z ⁻¹ᵁ M.off) : IsGenericPoint (ptOf z) Set.univ := by
  refine Set.eq_univ_of_univ_subset ?_
  rw [← M.dense.closure_eq]
  refine closure_minimal (fun y hy => ?_) isClosed_closure
  refine specializes_iff_mem_closure.1 ?_
  have hy' : y ∈ M.opn := hy
  have hyU : M.σ y ∈ U₀ X Z := hy'
  have hF : toFlag M y ∈ flagOpen X := hyU
  have hY : toFlag M y ∈ X.π ⁻¹ᵁ barComp Y Z := (M.σ y).2
  have hO' : ⊤ ≤ (resPt y ≫ toFlag M) ⁻¹ᵁ flagOpen X := by
    refine (le_iff_ptOf_mem _ _).2 ?_
    rw [ptOf_comp, ptOf_resPt]
    exact hF
  obtain ⟨_, hch⟩ := exists_chartFr _ hO'
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (X.F.cover.ge (Set.mem_univ (toFlag M y)))
  have hk' : ⊤ ≤ (resPt y ≫ toFlag M) ⁻¹ᵁ X.F.U k := by
    refine (le_iff_ptOf_mem _ _).2 ?_
    rw [ptOf_comp, ptOf_resPt]
    exact hk
  obtain ⟨Q, hQ⟩ := hch k hk'
  have e : resPt y ≫ toFlag M = X.ptY Q := FlagCover.eq_ptY hQ.lies
  have hQZ : LiesOn Z Q := by
    refine (ptY_le_iff X Z Q).1 ((le_iff_ptOf_mem _ _).2 ?_)
    rw [← e, ptOf_comp, ptOf_resPt]
    exact hY
  have sp := specializes_ptY_genFr X Z h Q hQZ
  rw [← hz, ← e, ptOf_comp, ptOf_comp, ptOf_resPt] at sp
  have : IsOpenImmersion (M.opn.ι ≫ M.σ) := by
    rw [← morphismRestrict_ι]
    have := M.iso
    infer_instance
  have hg : IsOpenImmersion (M.opn.ι ≫ toFlag M) := by
    rw [toFlag, ← Category.assoc]
    infer_instance
  have hz' : ptOf z ∈ M.opn := by
    have := (le_iff_ptOf_mem _ _).1 hO
    rwa [M.off_eq] at this
  have sp' : (⟨ptOf z, hz'⟩ : M.opn) ⤳ ⟨y, hy'⟩ :=
    (M.opn.ι ≫ toFlag M).isOpenEmbedding.isInducing.specializes_iff.1 sp
  exact sp'.map continuous_subtype_val

end Generic

section Coords

variable {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem val_restr' {k : Type} [CommRing k] {T : Scheme.{0}} {p : T ⟶ Sp k} {B : LB T} {O O' : T.Opens} (h : O' ≤ O)
    {A : Type} [CommRing A] (x : Sp A ⟶ T) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O') (hi : ⊤ ≤ x ⁻¹ᵁ B.U i)
    (f : H0 p B O) : H0.val x i hO' hi (restr h f) = H0.val x i hO hi f :=
  evalPt_res x (inf_le_inf_right _ h) (GlobalTheory.FlagMod.le_preimage_inf hO hi) (GlobalTheory.FlagMod.le_preimage_inf hO' hi) _

theorem valR_eq_evalPt {A : Type} [CommRing A] {T : Scheme.{0}} (x : Sp A ⟶ T) (O : T.Opens) (h : ⊤ ≤ x ⁻¹ᵁ O)
    (f : Γ(T, O)) : valR x O f = evalPt x O h f := dif_pos h

theorem chartFr_congr {S : Type} [CommRing S] [Algebra c.F S] {k : X.F.J} {z z' : Sp S ⟶ X.YY} (e : z = z')
    {hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k} {hz' : ⊤ ≤ z' ⁻¹ᵁ X.F.U k} {Q : FrPt Xo c S} (h : X.F.ChartFr k z hz Q) :
    X.F.ChartFr k z' hz' Q := by
  subst e; exact h

theorem exists_chart_val (h : GenFrEx Xo c) {P : WtPar Dw} (R : Choice X Z U P) (hfree : FreeOnOpen X Z U P.u₁)
    {z : Sp (Om Z) ⟶ R.X} (hz : z ≫ toFlag R.toModif = X.ptY (genFr h Z)) (hO : ⊤ ≤ z ⁻¹ᵁ R.off) :
    ∃ (i : R.L.ι) (a : Om Z), ptOf z ∈ R.L.U i ∧ a ≠ 0 ∧ ∀ (g : Cusp Z U P.u₁) (w : space X Z U P.u₁),
      restr le_top w.1 = cuspSec X Z U P.u₁ g →
      valR z (R.L.U i) ((toSec (R.Δ₁.lift w)).f i) = a * genVal Z g.1 := by
  classical
  have e₁ : (z ≫ R.σ) ≫ inc₀ X Z = X.pt (genFr h Z) ≫ X.inc := by
    rw [Category.assoc, X.pt_inc]; exact hz
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (X.F.cover.ge (Set.mem_univ (ptOf ((z ≫ R.σ) ≫ inc₀ X Z))))
  have hk₂ : ⊤ ≤ ((z ≫ R.σ) ≫ inc₀ X Z) ⁻¹ᵁ X.F.U k := (le_iff_ptOf_mem _ _).2 hk
  have hk₁ : ⊤ ≤ (X.pt (genFr h Z) ≫ X.inc) ⁻¹ᵁ X.F.U k := e₁ ▸ hk₂
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor (genFr h Z) k hk₁
  have hQ₂ : X.F.ChartFr k ((z ≫ R.σ) ≫ inc₀ X Z) hk₂ Q := chartFr_congr e₁.symm hQ
  have hU : ⊤ ≤ (z ≫ R.σ) ⁻¹ᵁ U₀ X Z := by
    intro s _
    have := hO (Set.mem_univ s)
    rw [R.off_eq] at this
    exact this
  have hO₂ : ⊤ ≤ ((z ≫ R.σ) ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hU
  obtain ⟨n, hn⟩ := exists_chart R.Δ₁.isLB (ptOf z)
  have hz' : ptOf z ∈ R.off := (le_iff_ptOf_mem _ _).1 hO
  have hm : ptOf z ∈ ((L₀ X Z P.u₁).pull R.σ).U (flagIdx R.toModif P.u₁ k) := (R.com.mem _ _ _).2 hk
  have hi : ptOf z ∈ R.L.U (flagIdx R.toModif P.u₁ k, n) := ⟨hm, hn⟩
  have hτ : valR z _ (R.Δ₁.t.f n) ≠ 0 := (valR_ne_zero_iff z hn _).2
    ((mem_nonzeroLocus_iff_basicOpen R.Δ₁.t hn).1 ((R.Δ₁.mem_nonzeroLocus _).2 (R.notMem_support hfree _ hz')))
  obtain ⟨T, hT0, hT⟩ : ∃ T : Om Z, T ≠ 0 ∧ ∀ f : secZ Xo c (exOf Dw P.u₁ 0),
      evR Xo c f.1 (genFr h Z) = T * H0.val (B := X.LL (exOf Dw P.u₁ 0)) ((z ≫ R.σ) ≫ inc₀ X Z) k hO₂ hk₂ (secOf X _ f) :=
    ⟨_, Units.ne_zero _, fun f => evR_eq_val_secOf f hO₂ hQ₂ ht⟩
  refine ⟨(flagIdx R.toModif P.u₁ k, n), (valR z _ (R.Δ₁.t.f n) * T)⁻¹, hi, inv_ne_zero (mul_ne_zero hτ hT0),
    fun g w hw => ?_⟩
  have hTop : ⊤ ≤ z ⁻¹ᵁ (⊤ : R.X.Opens) := fun _ _ => trivial
  have hTop' : ⊤ ≤ (z ≫ R.σ) ⁻¹ᵁ (⊤ : (Y₀ X Z).Opens) := fun _ _ => trivial
  have hi' := (le_iff_ptOf_mem z _).2 hi
  have hm' := (le_iff_ptOf_mem z _).2 hm
  have hn' := (le_iff_ptOf_mem z _).2 hn
  have hm'' : ⊤ ≤ (z ≫ R.σ) ⁻¹ᵁ (L₀ X Z P.u₁).U (flagIdx R.toModif P.u₁ k PUnit.unit) := by
    have hm₀ : R.σ (ptOf z) ∈ (L₀ X Z P.u₁).U (flagIdx R.toModif P.u₁ k PUnit.unit) := mem_pull.1 hm
    exact (le_iff_ptOf_mem _ _).2 hm₀
  have v₁ : valR z (R.L.U (flagIdx R.toModif P.u₁ k, n)) ((toSec (R.Δ₁.lift w)).f (flagIdx R.toModif P.u₁ k, n)) =
      H0.val z _ hTop hi' (R.Δ₁.lift w) := by
    have := H0.val_ofSec (p := R.str) z (flagIdx R.toModif P.u₁ k, n) hTop hi' (toSec (R.Δ₁.lift w))
    rw [ofSec_toSec] at this
    rw [this, valR_eq_evalPt z _ hi']
  have v₂ := (divChart (LB.isLB_pull (isLB_L₀ X Z P.u₁) R.σ) R.Δ₁.isLB).val_mul (ofSec R.str ⊤ R.Δ₁.t) (R.Δ₁.lift w)
    (flagIdx R.toModif P.u₁ k, n) z hTop hn' hi' hm'
  have v₃ : H0.val z _ hTop hm' (H0.pull R.σ le_top w.1) = H0.val (z ≫ R.σ) _ hTop' hm'' w.1 :=
    H0.val_pull R.σ le_top z _ hTop hm' hTop' hm'' w.1
  have v₄ := val_restr' (p := str₀ X Z) (le_top : U₀ X Z ≤ ⊤) (z ≫ R.σ) _ hTop' hU hm'' w.1
  have v₅ : H0.val (z ≫ R.σ) _ hU hm'' (cuspSec X Z U P.u₁ g) = H0.val (B := X.LL (exOf Dw P.u₁ 0)) ((z ≫ R.σ) ≫ inc₀ X Z) k hO₂ hk₂
      (secOf X _ ⟨g.1, cusp_le_secZ Z U _ g.2⟩) :=
    H0.val_pull (inc₀ X Z) le_rfl (z ≫ R.σ) _ hU hm'' hO₂ hk₂ _
  have v₆ : genVal Z g.1 = evR Xo c g.1 (genFr h Z) := rfl
  have v₇ : H0.val z _ hTop hn' (ofSec R.str ⊤ R.Δ₁.t) = valR z _ (R.Δ₁.t.f n) := by
    rw [H0.val_ofSec, valR_eq_evalPt z _ hn']
  have v₈ := hT ⟨g.1, cusp_le_secZ Z U _ g.2⟩
  rw [v₁, v₆, v₈, ← v₅, ← hw, v₄, ← v₃, ← R.Δ₁.incl_lift w]
  have v₉ : H0.val z _ hTop hm' (R.Δ₁.incl ⊤ (R.Δ₁.lift w)) = valR z _ (R.Δ₁.t.f n) * H0.val z _ hTop hi' (R.Δ₁.lift w) :=
    v₂.trans (congrArg (· * _) v₇)
  rw [v₉]
  field_simp

end Coords

theorem compPresents_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), GlobalTheory.CompHt.CompPresents U x V dict Z (GlobalTheory.AllWt.wtOf Dw P.u₁ 0) (h.data f₁ f₂ th k).toHermSys := by
  intro E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k
  have hG : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  refine ⟨(dimFlag_eq Dw).symm, f₁.b, f₁.isFrame, ?_⟩
  obtain ⟨z, hz, hO⟩ := exists_lift_genFr R.toModif hG
  have hgen := isGenericPoint_of_lift R.toModif hG hz hO
  have hV := (R.isAlgebraicData R.Δ₁ h.ext₁.equiv f₁ (dense_U₀ X Z) h.conn h.one_le k.abelian₂).variety
  have : IsIntegral (h.data f₁ f₂ th k).toHermSys.toLinSys.Y := hV.isIntegral
  have hstr : z ≫ (h.data f₁ f₂ th k).toHermSys.toLinSys.str = spMap (algebraMap c.F (Om Z)) := by
    show z ≫ (toFlag R.toModif ≫ flagStr X) = _
    rw [← Category.assoc, hz, ptY_str]
  obtain ⟨i, a, hi, ha, hv⟩ := exists_chart_val hG R h.free₁ hz hO
  obtain ⟨b, hb, hb', -⟩ := (h.data f₁ f₂ th k).toHermSys.toLinSys.exists_frame_change z i hi
  refine GlobalTheory.CompHt.imageIdeal_eq_coneIdeal_of_generic c.F (Om Z) _ ⟨z, hstr⟩ hgen (b⁻¹ * a) _
    (mul_ne_zero (inv_ne_zero hb) ha) (funext fun j => ?_)
  have e₁ := hb' ((h.data f₁ f₂ th k).toHermSys.toLinSys.b j)
  have e₂ := hv (f₁.b j) (h.ext₁.equiv (f₁.b j)) (h.ext₁.restr_equiv _)
  have e₃ := e₁.symm.trans e₂
  show (h.data f₁ f₂ th k).toHermSys.toLinSys.val z _ = (b⁻¹ * a) * genVal Z (f₁.b j).1
  rw [mul_assoc, ← e₃, inv_mul_cancel_left₀ hb]

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorUniformizerExponent
section
open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

variable {k : Type*} [Field k]

def auxiliaryVectorUniformizerExponent (a a' : ℤ) (c : ℕ) {n : Type*} : n ⊕ Fin c → ℤ
  | .inl _ => 0
  | .inr p => a * ((c : ℤ) - p) - a' * ((p : ℤ) + 1)

def vtxExp (a a' : ℤ) (c t x : ℕ) : ℤ :=
  if t ≤ x then a * ((c : ℤ) - ((x - t : ℕ) : ℤ)) - a' * (((x - t : ℕ) : ℤ) + 1) else 0

variable (G : Grid k)

def colDiag (ϖ : kˣ) (a a' : ℤ) (j : ℕ) : GL (Fin (G.rank (G.m, j))) k :=
  diagGL fun x => ϖ ^ vtxExp a a' (G.m - 1 - j) (topRank G j) x

def boxExp (a a' : ℤ) (j : Fin (G.m - 1))
    (v : StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j))) : ℤ :=
  a - auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) v.1.2 + auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) v.1.1

variable [ValuativeRel k]

def box (ϖ : kˣ) (a a' : ℤ) : Set (Vars G) :=
  Set.univ.pi fun j => Set.univ.pi fun v => {x : k | valuation k x ≤ valuation k ((ϖ ^ boxExp G a a' j v : kˣ) : k)}

variable {G}

theorem moveArgs_one_diag (g : G.VertexGroup) (d : ∀ X : ℕ × ℕ, Fin (G.rank X) → kˣ)
    (hg : ∀ X, g X = diagGL (d X)) (z : G.Args) (b : Edge) (r : Fin (G.rank b.tgt)) (s : Fin (G.rank b.src)) :
    G.moveArgs .one g z b r s = (d b.tgt r : k) * z b r s * ((d b.src s)⁻¹ : kˣ) := by
  have h1 : ∀ X, ((g X)⁻¹).val = diagonal fun i => (((d X i)⁻¹ : kˣ) : k) := fun X => by rw [hg]; rfl
  simp only [Grid.moveArgs, Assignment.read, invT_inv_val, invT_val]
  rw [h1, hg, diagGL_val, diagonal_transpose, diagonal_transpose, mul_diagonal, diagonal_mul]

omit [ValuativeRel k] in

theorem vtxExp_frame (a a' : ℤ) {t c b : ℕ} (h : t + c = b) (y : Fin t ⊕ Fin c) :
    vtxExp a a' c t (frame h y) = auxiliaryVectorUniformizerExponent a a' c y := by
  rcases y with x | p
  · simp [vtxExp, auxiliaryVectorUniformizerExponent, frame, finSumFinEquiv_apply_left, x.2]
  · simp [vtxExp, auxiliaryVectorUniformizerExponent, frame, finSumFinEquiv_apply_right]

end GlobalTheory.OriginBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernAtTwoEqStatement
section
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernAt_two_eq_ofValuesTwo_chernTwo : ∀ {n : ℕ} (G : V n → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (v : V n), chernAt G v 2 = ofValuesTwo (chernTwo G v) := by
  first | exact @GlobalTheory.SecForm.chernAt_two_eq | exact GlobalTheory.SecForm.chernAt_two_eq | (intros; apply GlobalTheory.SecForm.chernAt_two_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnExtTraceStatement
section
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_extTrace_of_isPosFrame : ∀ {n : ℕ} {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set (V n)} {H : V n → Matrix (m ⊕ l) (m ⊕ l) ℂ}, IsPosFrame U H → ∀ ξ η : V n, ContDiffOn ℝ ∞ (fun v => extTrace H v ξ η) U := by
  first | exact @GlobalTheory.SecForm.contDiffOn_extTrace | exact GlobalTheory.SecForm.contDiffOn_extTrace | (intros; apply GlobalTheory.SecForm.contDiffOn_extTrace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarPullbackHolomorphicZeroStatement
section
open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_pullback_holomorphic_zero : ∀ {n m : ℕ} {φ : V n → V m} {U : Set (V n)}, IsOpen U → DifferentiableOn ℂ φ U → ∀ {v : V n}, v ∈ U → ∀ (θ : Alt m), dbarAt (fun x => pull (fderiv ℂ φ x) θ) v = 0 := by
  first | exact @GlobalTheory.CxForm.PullClosed.dbarAt_pull_fderiv | exact GlobalTheory.CxForm.PullClosed.dbarAt_pull_fderiv | (intros; apply GlobalTheory.CxForm.PullClosed.dbarAt_pull_fderiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcEqOfLocalEqStatement
section
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddc_eq_of_local_eq : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (α : A.Fld) (x : A.Pt) (f : V n → Alt n), A.loc α x.1.1 =ᶠ[𝓝 x.crd] f → A.ddc α x = kappa • delAt (dbarAt f) x.crd := by
  first | exact @GlobalTheory.SecForm.DdcGerm.ddc_eq_of_eventuallyEq | exact GlobalTheory.SecForm.DdcGerm.ddc_eq_of_eventuallyEq | (intros; apply GlobalTheory.SecForm.DdcGerm.ddc_eq_of_eventuallyEq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcOfValuesEqStatement
section
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddc_ofValues_eq : ∀ {n : ℕ} (α : V n → V n → V n → ℂ) (v : V n), (∀ a b, ContDiffAt ℝ 2 (fun x => α x (coordVec a) (coordVec b)) v) → kappa • delAt (dbarAt fun x => (ofValues (α x) : Alt n)) v = (ofValuesTwo (ddcForm α v) : Alt n) := by
  first | exact @GlobalTheory.SecForm.ddc_ofValues | exact GlobalTheory.SecForm.ddc_ofValues | (intros; apply GlobalTheory.SecForm.ddc_ofValues <;> assumption)
end

