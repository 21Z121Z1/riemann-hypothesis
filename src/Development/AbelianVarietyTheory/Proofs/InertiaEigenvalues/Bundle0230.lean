import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0223
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtensionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactGroup_rep_defined_over_finite_extension : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] (a : ℕ) (r : G →* Matrix.GeneralLinearGroup (Fin a) (Om l)), Continuous (fun g => ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → ∀ L₀ : FinExt l, ∃ L : FinExt l, L₀.1 ≤ L.1 ∧ ∀ g i j, ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1 := by
  first | exact @GlobalTheory.CompactRepField.exists_finExt_entries_mem | exact GlobalTheory.CompactRepField.exists_finExt_entries_mem | (intros; apply GlobalTheory.CompactRepField.exists_finExt_entries_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexFieldAutActsHarishChandraCharacters
section
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.FieldAut

section Rep

variable {G : Type} [Group G]

def galRep (σ : ℂ ≃+* ℂ) (V : FDRep ℂ G) : Representation ℂ G (Fin (Module.finrank ℂ V) → ℂ) :=
  ((Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin (Module.finrank ℂ V))).toMulEquiv.toMonoidHom).comp
    (((σ : ℂ →+* ℂ).mapMatrix (m := Fin (Module.finrank ℂ V))).toMonoidHom.comp
      (((LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ V)).toMulEquiv.toMonoidHom).comp V.ρ))

theorem trace_galRep (σ : ℂ ≃+* ℂ) (V : FDRep ℂ G) (x : G) :
    LinearMap.trace ℂ _ (galRep σ V x) = σ (V.character x) := by
  have h1 : galRep σ V x =
      Matrix.toLin' ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (V.ρ x)).map σ) := rfl
  have h2 : V.character x =
      (LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (V.ρ x)).trace :=
    LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V) (V.ρ x)
  rw [h1, Matrix.trace_toLin'_eq, h2]
  simp [Matrix.trace]

variable [Fintype G]

theorem isIrr_comp (σ : ℂ ≃+* ℂ) {χ : G → ℂ} (h : IsIrr χ) : IsIrr (σ ∘ χ) := by
  obtain ⟨V, hs, hV⟩ := h
  have hW : ∀ x, (FDRep.of (galRep σ V)).character x = σ (V.character x) := fun x => trace_galRep σ V x
  refine ⟨FDRep.of (galRep σ V), ?_, fun x => by rw [hW, hV]; rfl⟩
  rw [FDRep.simple_iff_char_is_norm_one]
  have h := congrArg σ ((FDRep.simple_iff_char_is_norm_one V).1 hs)
  rw [map_natCast, map_sum] at h
  rw [← h]
  exact Finset.sum_congr rfl fun x _ => by rw [map_mul, hW, hW]

theorem coeff_zOf (χ : G → ℂ) (y : G) :
    (zOf χ).coeff y = χ 1 / (Fintype.card G : ℂ) * χ y⁻¹ := by
  simp only [zOf, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mapRange_zOf (σ : ℂ ≃+* ℂ) (χ : G → ℂ) :
    (zOf χ).coeff.mapRange σ (map_zero σ) = (zOf (σ ∘ χ)).coeff := by
  ext y
  rw [Finsupp.mapRange_apply, coeff_zOf, coeff_zOf]
  simp only [Function.comp, map_mul, map_div₀, map_natCast]

theorem ip_comp (σ : ℂ ≃+* ℂ) (α β : G → ℂ) : ip (σ ∘ α) (σ ∘ β) = σ (ip α β) := by
  simp only [ip, Function.comp, map_mul, map_sum, map_inv₀, map_natCast]

end Rep

variable {g : ℕ} [Fact g.Prime]

theorem hc_comp (σ : ℂ ≃+* ℂ) (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (n : ℕ) :
    hc a b (σ ∘ α) (σ ∘ β) n = σ ∘ hc a b α β n := by
  funext x
  simp only [hc, hcT, Function.comp, map_mul, map_sum, map_inv₀, map_natCast, apply_ite σ, map_zero]

theorem degL_map (σ : ℂ ≃+* ℂ) (L : List (Pc g)) :
    degL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) = degL L := by
  simp [degL, List.map_map, Function.comp_def]

theorem hcL_map (σ : ℂ ≃+* ℂ) (L : List (Pc g)) :
    ∀ n, hcL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) n = σ ∘ hcL L n := by
  induction L with
  | nil =>
    intro n
    funext x
    simp [hcL_nil]
  | cons p L ih =>
    intro n
    show hc p.1 (degL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g))) (σ ∘ p.2)
      (hcL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) (degL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)))) n = _
    rw [degL_map, ih, hc_comp, hcL_cons]

theorem res_comp (σ : ℂ ≃+* ℂ) (a b : ℕ) {n : ℕ} (χ : Gn g n → ℂ) (h₁ : Gn g a) (h₂ : Gn g b) :
    res a b (σ ∘ χ) h₁ h₂ = σ (res a b χ h₁ h₂) := by
  simp only [res, Function.comp, map_mul, map_sum, map_inv₀, map_pow, map_natCast, apply_ite σ, map_zero]

theorem isCusp_comp (σ : ℂ ≃+* ℂ) {d : ℕ} {χ : Gn g d → ℂ} (h : IsCusp χ) : IsCusp (σ ∘ χ) :=
  ⟨h.1, isIrr_comp σ h.2.1, fun a ha ha' => by rw [res_comp, h.2.2 a ha ha', map_zero]⟩

end GlobalTheory.CompanionTheory.FieldAut

theorem GlobalTheory.CompanionTheory.FieldAut.action : ∀ (g : ℕ) [Fact g.Prime] (σ : ℂ ≃+* ℂ), (∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ), (IsIrr χ → IsIrr (σ ∘ χ)) ∧ (zOf χ).coeff.mapRange σ (map_zero σ) = (zOf (σ ∘ χ)).coeff ∧ ∀ β, ip (σ ∘ χ) (σ ∘ β) = σ (ip χ β)) ∧ (∀ (L : List (Pc g)) (n : ℕ), hcL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) n = σ ∘ hcL L n) ∧ ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → IsCusp (σ ∘ χ) := by
  intro g _ σ
  exact ⟨fun G _ _ χ => ⟨GlobalTheory.CompanionTheory.FieldAut.isIrr_comp σ, GlobalTheory.CompanionTheory.FieldAut.mapRange_zOf σ χ,
    GlobalTheory.CompanionTheory.FieldAut.ip_comp σ χ⟩, fun L n => GlobalTheory.CompanionTheory.FieldAut.hcL_map σ L n,
    fun d χ h => GlobalTheory.CompanionTheory.FieldAut.isCusp_comp σ h⟩

end
end

section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
theorem _root_.GlobalTheory.Adopt.complexFieldAut_acts_harishChandra_characters : ∀ (g : ℕ) [Fact g.Prime] (σ : ℂ ≃+* ℂ), (∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ), (IsIrr χ → IsIrr (σ ∘ χ)) ∧ (zOf χ).coeff.mapRange σ (map_zero σ) = (zOf (σ ∘ χ)).coeff ∧ ∀ β, ip (σ ∘ χ) (σ ∘ β) = σ (ip χ β)) ∧ (∀ (L : List (Pc g)) (n : ℕ), hcL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) n = σ ∘ hcL L n) ∧ ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → IsCusp (σ ∘ χ) := by
  first | exact @GlobalTheory.CompanionTheory.FieldAut.action | exact GlobalTheory.CompanionTheory.FieldAut.action | (intros; apply GlobalTheory.CompanionTheory.FieldAut.action <;> assumption)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMulLeftDvr
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass

theorem continuous_of_mul_left_dvr {O X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [TopologicalSpace X]
    (hO : IsAdic (IsLocalRing.maximalIdeal O)) {a : O} (ha : a ≠ 0) {f : X → O}
    (hf : Continuous fun x => a * f x) : Continuous f := by
  obtain ⟨hopen, hbasis⟩ := isAdic_iff.1 hO
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hm := hϖ.maximalIdeal_eq
  rw [continuous_iff_continuousAt]
  intro x0
  have h0 : Filter.Tendsto (fun x => f x - f x0) (nhds x0) (nhds 0) := by
    intro s hs
    obtain ⟨n, hn⟩ := hbasis s hs
    have h1 : Continuous fun x => (u : O) * ϖ ^ k * f x - (u : O) * ϖ ^ k * f x0 := hf.sub continuous_const
    have h2 := (h1.isOpen_preimage _ (hopen (k + n))).mem_nhds (x := x0) (by simp)
    rw [Filter.mem_map]
    filter_upwards [h2] with x hx
    apply hn
    simp only [Set.mem_preimage, SetLike.mem_coe, hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx ⊢
    rw [← mul_sub, pow_add, mul_assoc, u.isUnit.dvd_mul_left, mul_dvd_mul_iff_left (pow_ne_zero k hϖ.ne_zero)] at hx
    exact hx
  have := h0.add_const (f x0)
  simpa [ContinuousAt] using this

theorem continuous_of_coeff_dvr {O X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [TopologicalSpace X]
    (hO : IsAdic (IsLocalRing.maximalIdeal O)) {n : ℕ} {M : X → Matrix (Fin n) (Fin n) O} (hM : Continuous M)
    (L : (Fin n → FractionRing O) →ₗ[FractionRing O] FractionRing O) (v : Fin n → FractionRing O) {f : X → O}
    (hf : ∀ x, algebraMap O (FractionRing O) (f x) = L (((M x).map (algebraMap O (FractionRing O))).mulVec v)) :
    Continuous f := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
    (fun p : Fin n × Fin n => L (Pi.single p.1 1) * v p.2)
  choose d hd using hb
  refine continuous_of_mul_left_dvr hO (nonZeroDivisors.coe_ne_zero b) ?_
  have : (fun x => (b : O) * f x) = fun x => ∑ p, ∑ q, d (p, q) * M x p q := by
    funext x
    apply IsFractionRing.injective O (FractionRing O)
    rw [map_mul, hf, LinearMap.pi_apply_eq_sum_univ L]
    simp only [map_sum, map_mul, hd, Finset.mul_sum, Matrix.mulVec, dotProduct, Matrix.map_apply, smul_eq_mul,
      Finset.sum_mul, Algebra.smul_def]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    have : (fun j => if p = j then (1 : FractionRing O) else 0) = Pi.single p 1 := by
      funext j; simp [Pi.single_apply, eq_comm]
    rw [this]; ring
  rw [this]
  fun_prop

theorem mapM_twistM_mulVec {O S Γ : Type} [CommRing O] [CommRing S] [Group Γ] {k : ℕ} (f : O →+* S)
    (M : Γ →* Matrix (Fin k) (Fin k) O) (χ : Γ →* Oˣ) (g : Γ) (v : Fin k → S) :
    (mapM f (twistM M χ) g).mulVec v = f (χ g : O) • (mapM f M g).mulVec v := by
  rw [← Matrix.smul_mulVec]
  congr 1
  ext p q
  simp [mapM, twistM]

theorem subTw_blocks : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GoodR D.nd i r → ∀ (π : D.nd.X i) (e : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i))), (∀ g u, e ((mapM (toK D.nd i) (rO D.nd i r π) g).mulVec u) = ((mapM (toK D.nd i) (rhoO D.nd i ρ π) g).mulVec (e u).1, fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * (e u).2 c)) → ∀ Xs : Set (D.nd.X i), π ∈ Xs → SubTw i r Xs (WpO D.nd i ρ π) ∧ ∀ c ∈ Finset.Icc 1 D.R.t, SubTw i r Xs (chiRatO D.nd i c) := by
  intro D i r ρ hr π e he Xs hπ
  have hO := D.nd.O_adic i
  have hrc : Continuous fun g => rO D.nd i r π g := (hr π).1
  have hχ : ∀ c, Continuous fun g => ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i) := fun c => D.nd.chi_cont i c
  have hχi : Continuous fun g => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) := by
    have := (hχ 1).comp (continuous_inv (G := GE D.nd))
    refine this.congr fun g => ?_
    simp
  have hρc : Continuous fun g => rhoO D.nd i ρ π g := by
    refine continuous_matrix fun p q => ?_
    refine continuous_of_coeff_dvr hO hrc
      ((LinearMap.proj p).comp ((LinearMap.fst _ _ _).comp e.toLinearMap)) (e.symm (Pi.single q 1, 0)) fun g => ?_
    have := congrArg (fun z => z.1 p) (he g (e.symm (Pi.single q 1, 0)))
    simp only [LinearEquiv.apply_symm_apply, Matrix.mulVec_single_one] at this
    exact this.symm
  refine ⟨⟨hχi.smul hρc, π, hπ, e.symm.toLinearMap.comp (LinearMap.inl _ _ _),
    e.symm.injective.comp LinearMap.inl_injective, fun g v => ?_⟩, fun c hc => ?_⟩
  · rw [WpO, rTwO, mapM_twistM_mulVec, mapM_twistM_mulVec, map_smul]
    congr 1
    apply e.injective
    rw [he]
    simp
    rfl
  · obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.1 hc
    let c' : Fin D.R.t := ⟨c - 1, by omega⟩
    have hcc : (c' : ℕ) + 1 = c := by simp only [c']; omega
    refine ⟨?_, π, hπ, e.symm.toLinearMap.comp ((LinearMap.inr _ _ _).comp
      ((LinearMap.single _ (fun _ => KK D.nd i) c').comp (LinearMap.proj 0))), ?_, fun g v => ?_⟩
    · have : Continuous fun g => (((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i) *
          (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i)) • (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) :=
        ((hχ c).mul hχi).smul continuous_const
      exact this
    · intro v w h
      have h1 := congrArg (fun z => (e z).2 c') h
      funext j
      rw [Subsingleton.elim j 0]
      simpa using h1
    · rw [chiRatO, rTwO, mapM_twistM_mulVec, mapM_twistM_mulVec, map_smul, MonoidHom.mul_apply, Units.val_mul,
        map_mul, mul_comm, mul_smul]
      congr 1
      apply e.injective
      rw [he, map_smul]
      ext j
      · simp
      · by_cases hj : j = c'
        · subst hj
          simp [hcc, mapM, Algebra.smul_def]
        · simp [hj]

end GlobalTheory.Pass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupOneCocyclesAnticommUpToCoboundaryStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_one_cocycles_anticomm_up_to_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∀ a ∈ continuousCocycles A.ρ, ∀ b ∈ continuousCocycles A'.ρ, (CobL (P.PD K) (cupL A'.ρ m a b) ↔ CobL (P.PD K) (cupL A.ρ m.flip b a)) ∧ (a ∈ B1 A.ρ ∨ b ∈ B1 A'.ρ → CobL (P.PD K) (cupL A'.ρ m a b)) := by
  first | exact @GlobalTheory.cupL_anticomm_cobL | exact GlobalTheory.cupL_anticomm_cobL | (intros; apply GlobalTheory.cupL_anticomm_cobL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilInvariantJumpDescendsFinExt
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.InvDescent

theorem exists_invariant_of_subgroup {G F Ω V : Type} [Group G] [Field F] [Field Ω]
    [AddCommGroup V] [Module Ω V] (H : Subgroup G) [Finite (G ⧸ H)]
    (ι : F →* Ω) (σ : G → Ω →* Ω) (hσ : ∀ g h c, σ (g * h) c = σ g (σ h c))
    (hσ1 : ∀ c, σ 1 c = c)
    (hH : ∀ g, g ∈ H ↔ ∀ c, σ g (ι c) = ι c)
    (A : G → V →+ V) (hA : ∀ g h v, A (g * h) v = A g (A h v))
    (hAs : ∀ g (c : Ω) v, A g (c • v) = σ g c • A g v)
    (N₀ N₁ : Submodule Ω V) (hN : ∀ g, ∀ v ∈ N₀, A g v ∈ N₀)
    (y : V) (hy : ∀ h ∈ H, A h y = y) (h0 : y ∈ N₀) (h1 : y ∉ N₁) :
    ∃ z, (∀ g, A g z = z) ∧ z ∈ N₀ ∧ z ∉ N₁ := by
  classical
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite _

  have key : ∀ (v : V), (∀ h ∈ H, A h v = v) → ∀ g g' : G,
      (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk g' → A g v = A g' v := by
    intro v hv g g' hgg'
    obtain ⟨h, hh, rfl⟩ : ∃ h ∈ H, g' = g * h :=
      ⟨g⁻¹ * g', QuotientGroup.eq.mp hgg', by group⟩
    rw [hA, hv h hh]
  have hfix : ∀ c : F, ∀ h ∈ H, A h (ι c • y) = ι c • y := by
    intro c h hh
    rw [hAs, hy h hh, ((hH h).mp hh) c]

  let T : F → V := fun c => ∑ q : G ⧸ H, A q.out (ι c • y)
  have hTinv : ∀ c g, A g (T c) = T c := by
    intro c g
    simp only [T, map_sum, ← hA]
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun q => ?_)
    apply key _ (hfix c)
    rw [MulAction.toPerm_apply, QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]
  have hT0 : ∀ c, T c ∈ N₀ := by
    intro c
    refine Submodule.sum_mem _ (fun q _ => ?_)
    rw [hAs]
    exact N₀.smul_mem _ (hN _ _ h0)
  by_contra hcon
  push Not at hcon
  have hT1 : ∀ c, T c ∈ N₁ := fun c => hcon (T c) (hTinv c) (hT0 c)

  let χ : G ⧸ H → (F →* Ω) := fun q => (σ q.out).comp ι
  have hσinv : ∀ g x, σ g⁻¹ (σ g x) = x := by
    intro g x
    rw [← hσ, inv_mul_cancel, hσ1]
  have hχ : Function.Injective χ := by
    intro q q' hqq'
    have hcq : ∀ c : F, σ q.out (ι c) = σ q'.out (ι c) := fun c => DFunLike.congr_fun hqq' c
    have hmem : q.out⁻¹ * q'.out ∈ H := by
      rw [hH]
      intro c
      rw [hσ, ← hcq, hσinv]
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    exact QuotientGroup.eq.mpr hmem
  have hli : LinearIndependent Ω (fun q => (χ q : F → Ω)) :=
    (linearIndependent_monoidHom F Ω).comp χ hχ

  let w : G ⧸ H → V ⧸ N₁ := fun q => N₁.mkQ (A q.out y)
  have hrel : ∀ c : F, ∑ q, χ q c • w q = 0 := by
    intro c
    have hz := (Submodule.Quotient.mk_eq_zero N₁).mpr (hT1 c)
    simp only [T, hAs] at hz
    rw [← Submodule.mkQ_apply, map_sum] at hz
    simpa [χ, w] using hz
  have hw : ∀ q, w q = 0 := by
    intro q
    rw [← Module.forall_dual_apply_eq_zero_iff Ω]
    intro φ
    have hsum : ∑ q', φ (w q') • (χ q' : F → Ω) = 0 := by
      funext c
      have hcq := congrArg φ (hrel c)
      simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hcq
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← hcq]
      exact Finset.sum_congr rfl (fun q' _ => mul_comm _ _)
    exact Fintype.linearIndependent_iff.mp hli _ hsum q
  have hy1 : A (QuotientGroup.mk (1 : G) : G ⧸ H).out y = y := by
    rw [key y hy _ 1 (QuotientGroup.out_eq' _)]
    exact hy 1 H.one_mem
  have hw1 := hw (QuotientGroup.mk 1)
  simp only [w, Submodule.mkQ_apply, hy1, Submodule.Quotient.mk_eq_zero] at hw1
  exact h1 hw1

variable {l : ℕ} [Fact l.Prime]

theorem smul_mem_Fil (P : LocPrime l) (K : FinExt l) (a : ℤ) (c : Om l) {x : P.R.BdR}
    (hx : x ∈ (P.PD K).Fil a) : c • x ∈ (P.PD K).Fil a := by

  have hint : IsIntegral ℚ_[l] c := (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
  obtain ⟨K', hcK⟩ : ∃ K' : FinExt l, c ∈ K'.1 :=
    ⟨⟨IntermediateField.adjoin ℚ_[l] {c}, IntermediateField.adjoin.finiteDimensional hint⟩,
      IntermediateField.mem_adjoin_simple_self ℚ_[l] c⟩
  have hx' : x ∈ (P.PD K').Fil a := by
    rw [← SetLike.mem_coe, ← P.PD_Fil K K' a]
    exact hx
  rw [← SetLike.mem_coe, P.PD_Fil K K' a, SetLike.mem_coe]
  exact ((P.PD K').Fil a).smul_mem (⟨c, hcK⟩ : K'.1) hx'

def filOm (P : LocPrime l) (K : FinExt l) (a : ℤ) : Submodule (Om l) P.R.BdR where
  carrier := ((P.PD K).Fil a : Set P.R.BdR)
  zero_mem' := ((P.PD K).Fil a).zero_mem
  add_mem' := fun h h' => ((P.PD K).Fil a).add_mem h h'
  smul_mem' := fun c _ hx => smul_mem_Fil P K a c hx

theorem finite_quot (K E : FinExt l) : Finite (↥(GK K) ⧸ (GK E).subgroupOf (GK K)) := by
  classical
  have : FiniteDimensional ℚ_[l] E.1 := E.2

  let f : (↥(GK K) ⧸ (GK E).subgroupOf (GK K)) → (E.1 →ₐ[ℚ_[l]] Om l) :=
    fun q => ((q.out : GQ l) : Om l →ₐ[ℚ_[l]] Om l).comp E.1.val
  refine Finite.of_injective f (fun q q' hqq' => ?_)
  have hres : ∀ x : E.1, (q.out : GQ l) x = (q'.out : GQ l) x := fun x => DFunLike.congr_fun hqq' x
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
  refine QuotientGroup.eq.mpr ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  change _ ∈ IntermediateField.fixingSubgroup E.1
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hx' := hres ⟨x, hx⟩
  simp only at hx'
  rw [AlgEquiv.mul_apply, ← hx']
  exact AlgEquiv.symm_apply_apply _ _

theorem jump_descends (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K E : FinExt l) (_hKE : K.1 ≤ E.1)
    (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) ℚ_[l])
    (hM : ∀ g ∈ GK K, ∀ h ∈ GK K, M (g * h) = M g * M h) (a : ℤ) (y : Fin d → P.R.BdR)
    (hy : ∀ g ∈ GK E, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec
      (fun i => P.actQdR g (y i)) = y)
    (h0 : ∀ i, y i ∈ (P.PD K).Fil a) (h1 : ¬ (∀ i, y i ∈ (P.PD K).Fil (a + 1))) :
    ∃ z : Fin d → P.R.BdR, (∀ g ∈ GK K, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec
      (fun i => P.actQdR g (z i)) = z) ∧ (∀ i, z i ∈ (P.PD K).Fil a) ∧
      ¬ (∀ i, z i ∈ (P.PD K).Fil (a + 1)) := by
  have := finite_quot K E
  let am := algebraMap ℚ_[l] P.R.BdR

  let A : ↥(GK K) → (Fin d → P.R.BdR) →+ (Fin d → P.R.BdR) := fun g =>
    AddMonoidHom.mk' (fun v => ((M g).map am).mulVec (fun i => P.actQdR g (v i)))
      (fun v w => by simp only [Pi.add_apply, map_add]; exact Matrix.mulVec_add _ _ _)
  have hAapp : ∀ g v, A g v = ((M g).map am).mulVec (fun i => P.actQdR g (v i)) := fun _ _ => rfl
  let σ : ↥(GK K) → Om l →* Om l := fun g => MonoidHomClass.toMonoidHom (g : GQ l)
  let ι : ↥E.1 →* Om l := MonoidHomClass.toMonoidHom E.1.val
  have hσ : ∀ g h c, σ (g * h) c = σ g (σ h c) := fun g h c => by
    simp only [σ, MonoidHom.coe_coe, Subgroup.coe_mul, AlgEquiv.mul_apply]
  have hσ1 : ∀ c, σ 1 c = c := fun c => by
    simp only [σ, MonoidHom.coe_coe, OneMemClass.coe_one, AlgEquiv.one_apply]
  have hH : ∀ g, g ∈ (GK E).subgroupOf (GK K) ↔ ∀ c, σ g (ι c) = ι c := by
    intro g
    rw [Subgroup.mem_subgroupOf]
    unfold GK
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h c => h c c.2, fun h x hx => h ⟨x, hx⟩⟩
  have hcomm : ∀ (f : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) (N : Matrix (Fin d) (Fin d) ℚ_[l])
      (w : Fin d → P.R.BdR), (fun i => f ((N.map am).mulVec w i)) = (N.map am).mulVec (fun i => f (w i)) := by
    intro f N w
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, am, AlgEquiv.commutes]
  have hA : ∀ g h v, A (g * h) v = A g (A h v) := by
    intro g h v
    rw [hAapp, hAapp, hAapp, hcomm, Matrix.mulVec_mulVec, ← Matrix.map_mul,
      ← hM g g.2 h h.2, Subgroup.coe_mul]
    congr 1
    funext i
    rw [map_mul, AlgEquiv.mul_apply]
  have hAs : ∀ g (c : Om l) v, A g (c • v) = σ g c • A g v := by
    intro g c v
    rw [hAapp, hAapp]
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, Algebra.smul_def,
      map_mul, P.actQdR_Om, Finset.mul_sum, σ, MonoidHom.coe_coe]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  let N₀ : Submodule (Om l) (Fin d → P.R.BdR) := Submodule.pi Set.univ (fun _ => filOm P K a)
  let N₁ : Submodule (Om l) (Fin d → P.R.BdR) := Submodule.pi Set.univ (fun _ => filOm P K (a + 1))
  have hmem : ∀ (b : ℤ) (v : Fin d → P.R.BdR),
      v ∈ Submodule.pi Set.univ (fun _ => filOm P K b) ↔ ∀ i, v i ∈ (P.PD K).Fil b := by
    intro b v
    simp only [Submodule.mem_pi, Set.mem_univ, true_imp_iff]
    rfl
  have hN : ∀ g, ∀ v ∈ N₀, A g v ∈ N₀ := by
    intro g v hv
    rw [hmem] at hv ⊢
    intro i
    rw [hAapp]
    simp only [Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    have hj : P.actQdR g (v j) ∈ (P.PD K).Fil a := by
      rw [← P.PD_actdR K g]
      exact (P.PD K).Fil_G g a _ (hv j)
    rw [Matrix.map_apply, ← Algebra.smul_def]
    exact Submodule.smul_of_tower_mem _ _ hj
  obtain ⟨z, hzA, hz0, hz1⟩ := exists_invariant_of_subgroup ((GK E).subgroupOf (GK K)) ι σ hσ hσ1 hH
    A hA hAs N₀ N₁ hN y (fun h hh => hy h ((Subgroup.mem_subgroupOf).mp hh)) ((hmem a y).mpr h0)
    (fun h => h1 ((hmem (a + 1) y).mp h))
  exact ⟨z, fun g hg => hzA ⟨g, hg⟩, (hmem a z).mp hz0, fun h => hz1 ((hmem (a + 1) z).mpr h)⟩

end GlobalTheory.InvDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilQuotientXiPowerAinfStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_fil_quotient_xi_power_ainf : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (J : ThetaL P AI) (n : ℕ), (∀ x ∈ (P.PD (botExt l)).Fil 0, ∃ (k : ℕ) (a : Ainf l), (l : P.R.BdR) ^ k * x - P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ)) ∧ (∀ a : Ainf l, P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ) ↔ AI.ξ ^ n ∣ a) ∧ (∃ w ∈ (P.PD (botExt l)).Fil 0, P.ιB P.tB = P.ιB (AI.ιA AI.ξ) * w ∧ J.θ w = ((AI.ζ 1 : OC l) : PadicComplex l) - 1)  := by
  first | exact @GlobalTheory.BdRQuot.fil_quotient | exact GlobalTheory.BdRQuot.fil_quotient | (intros; apply GlobalTheory.BdRQuot.fil_quotient <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeStableTwistedPairingStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_stable_twisted_pairing : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (LA : Lattice (O := O) A.ρ), IsDual1 (P.PD K) A.ρ A'.ρ m → (∀ g, ∃ a : O, ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap O LL a) → ∃ LA' : Lattice (O := O) A'.ρ, IsDualLat1 (P.PD K) LA LA' m ∧ IsDualLat1 (P.PD K) LA' LA m.flip := by
  first | exact @GlobalTheory.DualLat.dualLattice_exists | exact GlobalTheory.DualLat.dualLattice_exists | (intros; apply GlobalTheory.DualLat.dualLattice_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExtEmbeddingSplittingStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finExt_embedding_splitting' : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL], ∃ LL' : FinExt l, Nonempty (LL →ₐ[ℚ_[l]] ↥LL'.1) ∧ Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL'.1) = finrank ℚ_[l] ↥K.1 ∧ Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL'.1) = finrank ℚ_[l] ↥(K0 K) := by
  first | exact @GlobalTheory.exists_finExt_embedding_splitting | exact GlobalTheory.exists_finExt_embedding_splitting | (intros; apply GlobalTheory.exists_finExt_embedding_splitting <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSimplePiecesStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_simple_pieces_sen_sum : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (B : Ob k G) (N : Lats k n B.m), M.Model B N → ∃ (s : ℕ) (C : Fin s → Ob k G) (L : ∀ a, Lats k n (C a).m), (∀ a, M.Model (C a) (L a)) ∧ (∀ a, IsSimpleModule (MonoidAlgebra k G) (C a).ρ.asModule) ∧ SameSS B.ρ (piRep fun a => (C a).ρ) ∧ ∀ i x, sen ((F.D B).γ i) (N i) x = ∑ a, sen ((F.D (C a)).γ i) (L a i) x := by
  first | exact @GlobalTheory.Models.ModTh.exists_simple_pieces | exact GlobalTheory.Models.ModTh.exists_simple_pieces | (intros; apply GlobalTheory.Models.ModTh.exists_simple_pieces <;> assumption)
end

