import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0008
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0007
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0008
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0004
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.DegreeL2RangeHypothesis
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma MeasureTheory
open scoped InnerProductSpace ENNReal

def deg_DSUniq : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (ν : Fin n → ℝ) (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    IsHCParam ν → IsDS ε ν σ → IsDS ε ν σ' →
      ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UJset ε, ∀ x, U (σ g x) = σ' g (U x)

def DegreeL2RangeHypothesis (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ (τ : D.what₂.Tau) (ν : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), IsHCParam ν →
    l1dist ν (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)),
      IsDS (epsSH D.R) ν σ → ∀ v w : H, IsKFin (epsSH D.R) σ v → IsKFin (epsSH D.R) σ w →
        MemLp (fun g : Formalism.REAL.UJ (epsSH D.R) => (frob (umat g) : ℂ) * coefOn σ v w g) 2 (Formalism.REAL.muG (epsSH D.R))

theorem deg_hc_add_single {n : ℕ} {μ : Fin n → ℝ} (h : IsHCParam μ) (hg : AllGaps μ 2) (s : Fin n) :
    IsHCParam (μ + Pi.single s 1) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · have h1 := h.1 hab
    have h2 := hg a b (ne_of_lt hab)
    rw [abs_of_pos (by linarith)] at h2
    have ha : (0 : ℝ) ≤ (Pi.single s (1 : ℝ) : Fin n → ℝ) a := by by_cases e : a = s <;> simp [Pi.single_apply, e]
    have hb : (Pi.single s (1 : ℝ) : Fin n → ℝ) b ≤ 1 := by by_cases e : b = s <;> simp [Pi.single_apply, e]
    simp only [Pi.add_apply]
    linarith
  · obtain ⟨m, hm⟩ := h.2 a
    by_cases e : a = s
    · subst e
      exact ⟨m + 1, by simp only [Pi.add_apply, Pi.single_eq_same]; push_cast; linarith⟩
    · exact ⟨m, by simp only [Pi.add_apply, Pi.single_eq_of_ne e, add_zero]; exact hm⟩

theorem deg_chain {n : ℕ} {ε : Fin n → Bool} (D : D7) (h18 : OnePlaceEstimates.adm18 D) (h90 : OnePlaceEstimates.FormalDegreeRatioAlt D) {μ : Fin n → ℝ}
    (hμ : IsHCParam μ) (hgap : ∀ I : Finset (Fin n), AllGaps (μ + epsI I) 2)
    (hL2 : ∀ I : Finset (Fin n), IsHCParam (μ + epsI I) → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε (μ + epsI I) σ →
      ∀ v w : H, IsKFin ε σ v → IsKFin ε σ w →
        MemLp (fun g : Formalism.REAL.UJ ε => (frob (umat g) : ℂ) * coefOn σ v w g) 2 (Formalism.REAL.muG ε))
    (H0 : Type) [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] [CompleteSpace H0]
    (σ0 : Matrix (Fin n) (Fin n) ℂ → (H0 →L[ℂ] H0)) (hDS0 : IsDS ε μ σ0) (v0 : H0) (hv0 : v0 ≠ 0)
    (hd0 : fdegOf (Formalism.REAL.muG ε) σ0 v0 ≠ 0) :
    ∀ I : Finset (Fin n), IsHCParam (μ + epsI I) →
      ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
        (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H), v ≠ 0 ∧ IsDS ε (μ + epsI I) σ ∧
          fdegOf (Formalism.REAL.muG ε) σ v / fdegOf (Formalism.REAL.muG ε) σ0 v0 = fdegHC (μ + epsI I) / fdegHC μ := by
  have hf0 := deg_fdeg_pos hμ
  refine deg_ind_up hμ _ ?_ ?_
  · refine ⟨H0, inferInstance, inferInstance, inferInstance, σ0, v0, hv0, ?_, ?_⟩
    · rw [deg_epsI_empty, add_zero]; exact hDS0
    · rw [deg_epsI_empty, add_zero, div_self hd0, div_self hf0.ne']
  · intro I a ha h1 h2 ih
    obtain ⟨H, i1, i2, i3, σ, v, hv, hDS, hr⟩ := ih
    obtain ⟨X, hX⟩ := h18 n ε (μ + epsI I) H σ h1 hDS (fun s => deg_hc_add_single h1 (hgap I) s)
    have haS : a ∈ X.Sm := (hX a).2 h2
    have hDSa := (X.ds a haS).2
    haveI : Nontrivial (X.Hs a) := hDSa.2.1
    obtain ⟨vs, hvs⟩ := exists_ne (0 : X.Hs a)
    have h9 := h90 n ε (μ + epsI I) H σ X h1 hDS (hL2 I h1 H σ hDS) a haS v vs hv hvs
    rw [← Formalism.QuantumDeterminants.fdegRatio n (μ + epsI I) a h1.1.injective (deg_hc_diff h1) h2.1.injective] at h9
    have hp1 := deg_fdeg_pos h1
    have hp2 := deg_fdeg_pos h2
    have hne : fdegOf (Formalism.REAL.muG ε) σ v ≠ 0 := by
      intro h0
      rw [h0, zero_div] at hr
      exact (div_pos hp1 hf0).ne hr
    refine ⟨X.Hs a, inferInstance, inferInstance, inferInstance, X.σs a, vs, hvs, ?_, ?_⟩
    · rw [deg_epsI_insert I a ha, ← add_assoc]; exact hDSa
    · rw [deg_epsI_insert I a ha, ← add_assoc]
      calc fdegOf (Formalism.REAL.muG ε) (X.σs a) vs / fdegOf (Formalism.REAL.muG ε) σ0 v0
          = (fdegOf (Formalism.REAL.muG ε) (X.σs a) vs / fdegOf (Formalism.REAL.muG ε) σ v) *
              (fdegOf (Formalism.REAL.muG ε) σ v / fdegOf (Formalism.REAL.muG ε) σ0 v0) := by field_simp
        _ = (fdegHC (μ + epsI I + Pi.single a 1) / fdegHC (μ + epsI I)) * (fdegHC (μ + epsI I) / fdegHC μ) := by
            rw [h9, hr]
        _ = fdegHC (μ + epsI I + Pi.single a 1) / fdegHC μ := by field_simp

theorem deg_datum (D : D7) {W : LocW D.R.k D.R.rS} {ν : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W}
    (hA : GoodS D ν A) : ∃ P : MatKR D.R.k D.R.rS, IsDS (epsSH D.R) ν (fun g => A.σ (P⁻¹ * g * P)) ∧
      ∀ v : A.H, v ≠ 0 → fdegOf (Formalism.REAL.muG (epsSH D.R)) (fun g => A.σ (P⁻¹ * g * P)) v =
        ((D.s.cdScale _ (epsSH D.R) : NNReal) : ℝ) * A.deg := by
  obtain ⟨_, ⟨P', hP', hDS⟩, _, _, _, _, _, _, _, _, P, hP, hF⟩ := hA
  refine ⟨P', hDS, fun v hv => ?_⟩
  have h1 := deg_isFdeg_cayley _ A.σ P P' hP hP'.1 hDS.2.2.1 A.deg hF
  rw [deg_fdegOf_smul (D.s.cdScale _ (epsSH D.R)) (D.s.cdScale_pos _ _), deg_fdegOf _ _ A.deg v h1 hv]

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FibreCountOfFirstSteps
section
noncomputable section

open scoped Classical Pointwise

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

theorem c3eqv_loc_mono {P : Ideal (𝓞 E)} [P.IsPrime] {L L' : Submodule (𝓞 E) S.V} (h : L ≤ L') :
    Formalism.HermitianLatticesTheory.localization₂ P L ≤ Formalism.HermitianLatticesTheory.localization₂ P L' := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := hx
  exact ⟨s, hs, h hx⟩

theorem c3eqv_le_loc {P : Ideal (𝓞 E)} [hP : P.IsPrime] (L : Submodule (𝓞 E) S.V) : L ≤ Formalism.HermitianLatticesTheory.localization₂ P L := by
  intro x hx
  exact ⟨1, P.primeCompl.one_mem, by rwa [one_smul]⟩

variable {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'}

end Gen

section Fin

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

end Fin

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfIsoAutCountGenus
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Tr

variable (D : D7)

theorem gmap_inf_cayley_degree_nondegeneracy {V : Type} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    [IsScalarTower (𝓞 D.host.E) D.host.E V] (g : V ≃ₗ[D.host.E] V) (A B : Submodule (𝓞 D.host.E) V) :
    gmap g (A ⊓ B) = gmap g A ⊓ gmap g B := by
  ext x
  simp only [isomAct_mem_gmap, Submodule.mem_inf]

theorem gmap_sup_cayley_degree_nondegeneracy {V : Type} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    [IsScalarTower (𝓞 D.host.E) D.host.E V] (g : V ≃ₗ[D.host.E] V) (A B : Submodule (𝓞 D.host.E) V) :
    gmap g (A ⊔ B) = gmap g A ⊔ gmap g B := Submodule.map_sup _ _ _

variable {D}

theorem isLattice_gmap_of_flag_isometry {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hσ : σ ∈ isom (VS D).hT) (hX : ∀ x ∈ F0.X, σ.symm x = x) (hz : σ.symm F0.z = F0.z) (Λ : LatV D)
    (hΛ : IsRowLat D F0 Λ) :
    IsRowLat D F0 (gmap σ Λ) ∧ Lsub (gmap σ Λ) (lf D F0) = gmap σ (Lsub Λ (lf D F0)) := by
  have hσ' : ∀ x y, (VS D).hT (σ x) (σ y) = (VS D).hT x y := hσ
  have hgX : gmap σ (toO (hS D) F0.X) = toO (hS D) F0.X := by
    ext x
    rw [isomAct_mem_gmap]
    constructor
    · intro h
      have h' : σ.symm x ∈ F0.X := h
      have := hX _ h'
      have e : σ.symm x = x := by
        apply σ.symm.injective
        exact this
      rw [e] at h
      exact h
    · intro h
      have h' : x ∈ F0.X := h
      rw [hX x h']
      exact h
  have hgO : gmap σ (toO (hS D) (orth (hS D) F0.X)) = toO (hS D) (orth (hS D) F0.X) := by
    ext y
    rw [isomAct_mem_gmap]
    change σ.symm y ∈ orth (hS D) F0.X ↔ y ∈ orth (hS D) F0.X
    rw [Formalism.MainNotions.mem_orth_iff, Formalism.MainNotions.mem_orth_iff]
    refine forall₂_congr fun x hx => ?_
    rw [← hσ' x (σ.symm y), LinearEquiv.apply_symm_apply]
    have : σ x = x := by
      rw [← LinearEquiv.eq_symm_apply, hX x hx]
    rw [this]
  have hXLam : XLam (gmap σ Λ) (lf D F0) = XLam Λ (lf D F0) := by
    have h1 : XLam (gmap σ Λ) (lf D F0) = gmap σ (XLam Λ (lf D F0)) := by
      unfold XLam
      rw [gmap_inf_cayley_degree_nondegeneracy]
      change gmap σ Λ ⊓ toO (hS D) F0.X = gmap σ Λ ⊓ gmap σ (toO (hS D) F0.X)
      rw [hgX]
    rw [h1]
    ext x
    rw [isomAct_mem_gmap]
    constructor
    · intro h
      have h' : σ.symm x ∈ F0.X := h.2
      have e : σ.symm x = x := σ.symm.injective (hX _ h')
      rw [e] at h
      exact h
    · intro h
      have h' : x ∈ F0.X := h.2
      rw [hX x h']
      exact h
  have hLsub : Lsub (gmap σ Λ) (lf D F0) = gmap σ (Lsub Λ (lf D F0)) := by
    unfold Lsub Lrep
    rw [gmap_inf_cayley_degree_nondegeneracy, gmap_sup_cayley_degree_nondegeneracy, gmap_inf_cayley_degree_nondegeneracy]
    change (gmap σ Λ ⊓ toO (hS D) (orth (hS D) F0.X) ⊔ toO (hS D) F0.X) ⊓ toO (hS D) (orth (hS D) F0.X) =
      (gmap σ Λ ⊓ gmap σ (toO (hS D) (orth (hS D) F0.X)) ⊔ gmap σ (toO (hS D) F0.X)) ⊓
        gmap σ (toO (hS D) (orth (hS D) F0.X))
    rw [hgX, hgO]
  refine ⟨?_, hLsub⟩
  obtain ⟨⟨hlat1, hgen1⟩, ⟨hL, hU, hLift, hConv⟩, hXS⟩ := hΛ
  obtain ⟨_, hloc, _, huni, _⟩ := isomAct (𝓞 D.host.E) D.host.E (VS D).V (VS D).hT σ hσ Λ
  refine ⟨⟨isomAct_lattice σ Λ hlat1, fun p hp => ?_⟩,
    ⟨isomAct_lattice σ Λ hL, huni.2 hU, ⟨?_, hLift.2⟩, ?_, fun c hc => hConv.2 c ?_⟩, hXLam.trans hXS⟩
  · obtain ⟨g, hg, e⟩ := hgen1 p hp
    exact ⟨σ * g, (isom (VS D).hT).mul_mem hσ hg, by rw [gmap_mul, e, hloc p]⟩
  · rw [isomAct_mem_gmap]
    change σ.symm F0.z ∈ Λ
    rw [hz]
    exact hLift.1
  · rw [hXLam]
    exact hConv.1
  · rw [hLsub, isomAct_mem_gmap, map_smul] at hc
    change c • σ.symm F0.z ∈ _ at hc
    rw [hz] at hc
    exact hc

variable (D)

theorem isometries_transport_lattices (u : D.what₂.Word) : IsometriesTransportLattices D u := by
  intro _ _ _ F0 he hz γ hγ Λ₁ hΛ₁
  have hzO : F0.z ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0)) := by
    rw [Formalism.MainNotions.mem_orth_iff]
    rintro _ ⟨w, rfl⟩
    rw [hz]
    exact Formalism.MainNotions.hT_swap_zero (z_orth_embedding D u w)
  have hXO : F0.X ≤ orth (hS D) (LinearMap.range (D.sp.iXY 0)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    rw [he]
    change D.sp.hypE a ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))
    rw [Formalism.MainNotions.mem_orth_iff]
    rintro _ ⟨w, rfl⟩
    exact (D.sp.hyp_orthX a w).1
  obtain ⟨hrow, hLsub⟩ := isLattice_gmap_of_flag_isometry F0 (extendByIdentity D γ) (extendByIdentity_mem_isom D γ hγ)
    (fun x hx => extendByIdentity_symm_fix_orth D γ x (hXO hx)) (extendByIdentity_symm_fix_orth D γ _ hzO) Λ₁ hΛ₁
  refine ⟨gmap (extendByIdentity D γ) Λ₁, hrow, ?_⟩
  ext ⟨w, c⟩
  unfold latticeWithZ
  rw [Submodule.mem_comap, hLsub, isomAct_mem_gmap, isomAct_mem_gmap, Submodule.mem_comap]
  have e1 : ((embedWithZ D F0).restrictScalars (𝓞 D.host.E)) (w, c) = D.sp.iXY 0 w + c • F0.z := by
    simp [embedWithZ]
  have e2 : ((embedWithZ D F0).restrictScalars (𝓞 D.host.E)) ((extendByOne D γ).symm (w, c)) =
      D.sp.iXY 0 (γ.symm w) + c • F0.z := by
    have : (extendByOne D γ).symm (w, c) = (γ.symm w, c) := rfl
    rw [this]
    simp [embedWithZ]
  rw [e1, e2, extendByIdentity_symm_apply D γ w _ (Submodule.smul_mem _ c hzO)]

theorem gluing_mass_of_iso_aut_count_genus (u : D.what₂.Word) (hpos : IsPosDef (D.sp.X 0).hT)
    (hlat : ForPrimeFlagLattice D u fun F0 Λ => Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)))
    (h1 : LatticeClassesIff D u) (h2 : CardAutEqCardIsometryStabilizer D u) (h4 : GluingCount D u)
    (h5 : OrthLatticesOneGenus D u) : WordRowsGluing D u :=
  gluing_mass_of_gluing_facts D u hpos hlat h1 h2 (isometries_transport_lattices D u) h4 h5

end Tr

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.MassLowerBoundOfMassFormula
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem det_orthLattice_eq_pow (D : D7) (u : D.what₂.Word) :
    ForPrimeFlagLattice D u fun F0 Λ => latDetH (D.sp.X 0).hT (L0X D Λ (lf D F0)) = ((Tu D u ^ D.R.f : ℕ) : ℝ) := by
  intro hTp h3 hsp F0 he hz Λ hrow
  obtain ⟨hΛ, hu, hlift, hconv⟩ := hrow.2.1
  obtain ⟨w₁, hw₁, hgen, hann⟩ := dual_orthLattice_quotient_cyclic F0 he hz Λ hΛ hu hlift.1 hconv.2 hTp.ne_zero
  refine latDet_of_cyclic_dual_quotient D _ (orthLattice_isLattice F0 he hz Λ hΛ hu) ?_ hTp hsp w₁ hw₁ hgen hann
  intro x hx
  exact (i_mem_dual _ _).2 fun y hy => orthLattice_isIntegral_of_unimodular Λ (lf D F0) hu y hy x hx

theorem orthLattice_structure (D : D7) (u : D.what₂.Word) : BaseLatticeStructure D u := orthLattice_structure_of_det D u (det_orthLattice_eq_pow D u)

theorem orth_space_posDef (D : D7) (u : D.what₂.Word) (hT : 0 < Tu D u) : IsPosDef (D.sp.X 0).hT :=
  orth_space_posDef_every_place (Formalism.MainNotions.S.Inh.tie_flag0 D u) rfl rfl hT

end Formalism.MainNotions.BridgeLemma₂

end
end

