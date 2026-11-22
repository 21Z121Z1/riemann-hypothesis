import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1837
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1461
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1841
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameDarbouxCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalSupportCommonDenominator
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.FinSupp

theorem finDiv_finPart_mul {F : Type} [Field F] [NumberField F] {N m : ℕ} {T : AF F} (hT : GlobalTheory.FinSupp.FinDiv F N ((m : AF F) * T))
    (a : 𝓞 F) : GlobalTheory.FinSupp.FinDiv F N (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F))) * T) := by
  intro v
  obtain ⟨b, hb, e⟩ := hT v
  have ha : algebraMap F (Fv F v) (a : F) ∈ v.adicCompletionIntegers F := HeightOneSpectrum.coe_mem_adicCompletionIntegers v a
  refine ⟨algebraMap F (Fv F v) (a : F) * b, mul_mem ha hb, ?_⟩
  have e1 : evFin F v (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F)))) =
      evFin F v (algebraMap F (AF F) ((m : F) * (a : F))) := rfl
  rw [map_mul, e1, AlgHom.commutes, map_mul, map_natCast]
  simp only [map_mul, map_natCast] at e
  rw [mul_comm ((m : Fv F v)) _, mul_assoc, e]
  ring

theorem finPart_mul {F : Type} [Field F] [NumberField F] (x y : AF F) :
    GlobalTheory.FinSupp.finPart F x * y = GlobalTheory.FinSupp.finPart F (x * y) :=
  Prod.ext (zero_mul _) rfl

theorem exists_common_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧
    ∀ ξ : Fin n × Fin d → F, om (g, h) Φ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  have S := hP.weil.isUSplitting
  have hstd : IsStd B.ψ := hP.base.std
  obtain ⟨N, hN1, hinv⟩ := GlobalTheory.T.adelicSchwartz_fixed_by_small_heisenberg_lattice F (Fin n × Fin d) B.ψ hstd.1 Φ hΦ
  obtain ⟨C, k, hC⟩ := GlobalTheory.T.exists_scale_movedHeisenbergLattice_polynomial_heights F E n d (Fin n × Fin d) M.co.e N hN1
  obtain ⟨D, hD1, hD⟩ := GlobalTheory.T.exists_bounded_denominator_standardChar_trivial F
  refine ⟨D * C, k, fun g h => ?_⟩
  obtain ⟨m, hm1, hmC, hmT⟩ := hC g.1 h.1
  refine ⟨D * m, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_, ?_⟩
  · push_cast
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hmC (by positivity)
  · intro ξ hξ i
    have key : ∀ a : 𝓞 F, B.ψ (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((a : F) * ((m : F) * ξ i)))) = 1 := by
      intro a
      set c : AF F := GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F))) with hc
      set y : Fin n × Fin d → AF F := c • Pi.single i 1 with hy
      set w' := M.co.e.symm (0, y) with hw'
      set p : UA σ X.J × UA σ W.J := (g, h) with hp
      set w := actAB (cA σ) p⁻¹ w' with hw
      have hwe : M.co.e w = c • M.co.e ((((g.1)⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) *
          M.co.e.symm (0, Pi.single i 1) * (((h.1⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ) := by
        rw [hw, hw', hy, hp]
        rw [show ((0 : Fin n × Fin d → AF F), c • Pi.single i (1 : AF F)) = c • ((0 : Fin n × Fin d → AF F), Pi.single i (1 : AF F)) by simp]
        rw [LinearEquiv.map_smul, ← LinearEquiv.map_smul M.co.e]
        congr 1
        simp only [actAB, Prod.inv_mk, Subgroup.coe_inv]
        rw [Matrix.mul_smul, Matrix.smul_mul]
      have hrho : M.co.rho B.ψ w Φ = Φ := by
        unfold Darboux.rho
        apply hinv
        intro l
        rw [hwe]
        obtain ⟨h1, h2⟩ := hmT i l
        refine ⟨?_, ?_, ?_, ?_⟩
        · show (c * _).1 = 0
          exact zero_mul _
        · rw [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
          exact finDiv_finPart_mul h1 a
        · show (c * _).1 = 0
          exact zero_mul _
        · rw [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
          exact finDiv_finPart_mul h2 a
      have himpl := S.impl p w Φ hΦ
      rw [hrho] at himpl
      have hact : actAB (cA σ) p w = w' := by
        rw [hw]
        simp only [actAB, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv, hp]
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
          Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
          Matrix.mul_one]
      rw [hact] at himpl
      have hx := congrFun himpl (fun j => algebraMap F (AF F) (ξ j))
      simp only [Darboux.rho, hw', LinearEquiv.apply_symm_apply, schr, zero_dotProduct, mul_zero, add_zero] at hx
      have h1 : B.ψ ((fun j => algebraMap F (AF F) (ξ j)) ⬝ᵥ y) = 1 := by
        have hne : om p Φ (fun j => algebraMap F (AF F) (ξ j)) ≠ 0 := hξ
        exact (mul_eq_right₀ hne).1 hx.symm
      rw [hy, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one, hc, finPart_mul, ← map_mul] at h1
      convert h1 using 3
      ring
    have := hD B.ψ hstd _ key
    convert this using 1
    push_cast
    ring

end GlobalTheory.FinSupp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationSeesawSchwartz
section
noncomputable section

namespace GlobalTheory.SWTrans

theorem exists_extend {G X : Type} [Monoid G] [AddCommGroup X] [Module ℂ X] (S : Submodule ℂ X)
    (ρ : G →* Module.End ℂ S) : ∃ om : G →* Module.End ℂ X, ∀ g (Φ : S), om g Φ.1 = (ρ g Φ).1 := by
  obtain ⟨C, hC⟩ := S.exists_isCompl
  let e := S.prodEquivOfIsCompl C hC
  let P : G →* Module.End ℂ (S × C) :=
    { toFun := fun g => LinearMap.prodMap (ρ g) LinearMap.id
      map_one' := by rw [map_one]; exact LinearMap.prodMap_one
      map_mul' := fun g h => by rw [map_mul, LinearMap.prodMap_mul]; rfl }
  refine ⟨(e.conjRingEquiv.toRingHom.toMonoidHom).comp P, fun g Φ => ?_⟩
  change e (P g (e.symm Φ.1)) = _
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
  simp [P, e]

theorem exists_trans {G H X Y : Type} [Monoid G] [Monoid H] (S : Submodule ℂ (X → ℂ)) (e : X ≃ Y) (a : H → X → X)
    (h1 : ∀ x, a 1 x = x) (hm : ∀ h h' x, a (h * h') x = a h' (a h x))
    (hS : ∀ h, ∀ Φ ∈ S, (fun x => Φ (a h x)) ∈ S) (ω : G →* Module.End ℂ S)
    (hc : ∀ h g (Φ Ψ : S), (∀ x, Ψ.1 x = Φ.1 (a h x)) → ∀ x, (ω g Ψ).1 x = (ω g Φ).1 (a h x)) :
    ∃ om : H × G →* Module.End ℂ (Y → ℂ), ∀ h g (φ : Y → ℂ) (Φ : S), φ ∘ e = Φ.1 →
      ∀ x, om (h, g) φ (e x) = (ω g Φ).1 (a h x) := by
  let L : H →* Module.End ℂ S :=
    { toFun := fun h => (LinearMap.funLeft ℂ ℂ (a h)).restrict (hS h)
      map_one' := by
        ext Φ x
        exact congrArg Φ.1 (h1 x)
      map_mul' := fun h h' => by
        ext Φ x
        exact congrArg Φ.1 (hm h h' x) }
  have hL : ∀ h g, Commute (L h) (ω g) := fun h g => by
    ext Φ x
    exact (hc h g Φ (L h Φ) (fun _ => rfl) x).symm
  obtain ⟨om, hom⟩ := exists_extend S (L.noncommCoprod ω hL)
  let c : (X → ℂ) ≃ₗ[ℂ] (Y → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ e.symm
  refine ⟨(c.conjRingEquiv.toRingHom.toMonoidHom).comp om, fun h g φ Φ hφ x => ?_⟩
  change om (h, g) (φ ∘ e) (e.symm (e x)) = _
  rw [hφ, hom, e.symm_apply_apply]
  rfl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

theorem exists_isTrans : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D), IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : GlobalTheory.StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n), GlobalTheory.StdUnn.IsWeilSch ψ χ θ V μ ω → ∀ (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E) (ι : UD D (-V.gram) ≃ₜ* GA D V) (κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n), ∃ om, IsTrans ε ι κ ω om := by
  intro D n V ψ χ θ hθ μ 𝓕 hμ ω hω J₂ d ε ι κ
  have key := GlobalTheory.WeilSchComm.subst_mem_and_comm D n V ψ χ θ hθ μ 𝓕 hμ ω hω
  obtain ⟨om, hom⟩ := exists_trans (H := UD D (-V.gram)) (schwartzA θ V.rank n) (coordL ε V.rank n).toEquiv
    (fun h x => (mt V (ι h)⁻¹ ⬝ x : Mx D V.rank n))
    (fun x => by simp only [map_one, inv_one, GlobalTheory.MixModel.mt_one, Matrix.one_mul])
    (fun h h' x => by simp only [map_mul, mul_inv_rev, GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc])
    (fun h => (key (ι h)⁻¹).1) (ω.comp κ.toMonoidHom) (fun h g => (key (ι h)⁻¹).2 (κ g))
  refine ⟨om, ?_, fun h g φ _ Φ hφ x => hom h g φ Φ hφ x⟩
  rintro ⟨h, g⟩ φ hφ
  have h1 := GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord D θ hθ V.rank n d ε ⟨φ, hφ⟩
  obtain ⟨φ', h2⟩ := GlobalTheory.SchwartzCoord.exists_schA_comp_coord_eq D θ hθ V.rank n d ε _
    ((key (ι h)⁻¹).1 _ (ω (κ g) ⟨_, h1⟩).2)
  have h3 : om (h, g) φ = φ'.1 := by
    funext y
    obtain ⟨x, rfl⟩ := (coord_bijective (m := V.rank) (n := n) ε).2 y
    exact (hom h g φ ⟨_, h1⟩ rfl x).trans (congrFun h2 x).symm
  rw [h3]
  exact φ'.2

end GlobalTheory.SWTrans

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittChangeBasisUnitaryIsoStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_change_basis_unitary_iso : ∀ (D : D7) (n : ℕ) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E), T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n → ∃ κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n, IsChartW T κ := by
  first | exact @GlobalTheory.SWLinkChart.exists_isChartW | exact GlobalTheory.SWLinkChart.exists_isChartW | (intros; apply GlobalTheory.SWLinkChart.exists_isChartW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameDarbouxCoordinatesStatement
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_frame_darboux_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
    ∃ (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d))
      (blk : Fin n × Fin d → Option (Fin r₀)),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
      (∀ i : Fin r₀, (Finset.univ.filter (fun j => blk j = some i)).card = 2 * d) ∧
      ∀ t : Fin r₀ → ℝ, (∀ i, 0 < t i) → ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        ∀ a' : UA σ X.J, (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a →
        ∀ z : Matrix (Fin n) (Fin d) (AE F E), co.e (mat a' * z) =
          (fun j => GlobalTheory.TorusTheta.infScale F (((blk j).elim 1 t)⁻¹) * (co.e z).1 j,
           fun j => GlobalTheory.TorusTheta.infScale F ((blk j).elim 1 t) * (co.e z).2 j) := by
  first | exact @GlobalTheory.TorusAdapted.adapted_torus | exact GlobalTheory.TorusAdapted.adapted_torus | (intros; apply GlobalTheory.TorusAdapted.adapted_torus <;> assumption)
end

