import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1474
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0939
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1343
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1492
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1471
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacter
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilVacChar

variable {D : D7}

theorem hecke_mul_inv {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) (h' : IsHeckeChar D χ') :
    IsHeckeChar D (χ * χ'⁻¹) := by
  refine ⟨?_, fun x => ?_⟩
  · change Continuous fun a => χ a * (χ' a)⁻¹
    exact h.1.mul h'.1.inv
  · change χ _ * (χ' _)⁻¹ = 1
    rw [h.2 x, h'.2 x, inv_one, mul_one]

theorem resEta_mul_inv {χ χ' : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (h' : ResEta D χ' n) :
    ResEta D (χ * χ'⁻¹) 0 := by
  refine ⟨h.1, fun η hη a => ?_⟩
  change χ _ * (χ' _)⁻¹ = _
  rw [h.2 η hη a, h'.2 η hη a, mul_inv_cancel, pow_zero]

theorem mul_mul_inv_cancel (χ χ' : (AE D)ˣ →* Circle) : χ' * (χ * χ'⁻¹) = χ := by
  refine MonoidHom.ext fun a => ?_
  change χ' a * (χ a * (χ' a)⁻¹) = χ a
  rw [mul_comm (χ a), mul_inv_cancel_left]

theorem vacuum_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (χS χT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))) (η : (AE D)ˣ →* Circle), IsEtaTilde D η → IsWeilDatumO ψ S T χS χT om → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, sS τ * compAt θ τ (Formalism.L2.Theta.mt S g) = compAt θ τ (Formalism.L2.Theta.mt S g) * sS τ) → (∀ τ, sT τ * compAt θ τ (Formalism.L2.Theta.mt T h) = compAt θ τ (Formalism.L2.Theta.mt T h) * sT τ) → ∀ x y, IsDetRoot S g x → IsDetRoot T h y → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → om (g, h) f = (((((χT * (η ^ T.rank)⁻¹) x)⁻¹ * (χS * (η ^ S.rank)⁻¹) y : Circle) : ℂ) * ∏ τ, detPlus (sS τ) (sT τ) (compAt θ τ (Formalism.L2.Theta.mt S g⁻¹)) (compAt θ τ (Formalism.L2.Theta.mt T h))) • f := by
  intro D ψ hψ S T θ hθ χS χT om η hη hom sS sT hS hT g hg h hh cS cT x y hx hy f hf hv
  obtain ⟨om₀, h₀, -, hvac⟩ := GlobalTheory.T.exists_weilDatum_powers_unramifiedEtaTilde D ψ hψ S T θ hθ _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame T) η hη
  obtain ⟨om', h', htw⟩ := GlobalTheory.T.exists_weilDatum_twist_heckeCharacters D ψ hψ S T _ _ (χS * (η ^ S.rank)⁻¹) (χT * (η ^ T.rank)⁻¹) om₀ h₀
    (hecke_mul_inv hom.hecS h₀.hecS) (hecke_mul_inv hom.hecT h₀.hecT)
    (resEta_mul_inv hom.resS h₀.resS) (resEta_mul_inv hom.resT h₀.resT)
  rw [mul_mul_inv_cancel, mul_mul_inv_cancel] at h'
  rw [GlobalTheory.T.weilDatum_unique_on_thetaFunctions D ψ hψ S T χS χT om om' hom h' (g, h) f hf, htw g h x y hx hy, LinearMap.smul_apply,
    hvac sS sT hS hT g hg h hh cS cT f hf hv, smul_smul]

end GlobalTheory.WeilVacChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepPureTensorLocalStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_rep_pure_tensor_local : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F)
    (w : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) w →
    ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ),
      (∀ᶠ u in cofinite, φ u = GlobalTheory.FinComm.indO u) →
      M.co.rho ψ w (pure f φ) =
        pure f (Function.update φ v (GlobalTheory.FinComm.locOp ψ v (GlobalTheory.FinComm.locPt v (M.co.e w)) (φ v))) := by
  first | exact @GlobalTheory.FinComm.RhoPure.rho_pure | exact GlobalTheory.FinComm.RhoPure.rho_pure | (intros; apply GlobalTheory.FinComm.RhoPure.rho_pure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepSliceFiniteOp
section
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

namespace GlobalTheory.VacLine.RhoSlice

variable {F : Type} [Field F] [NumberField F]

theorem at_mul {v : Pl F} {b : AF F} (hb : At (evFin F v) b) (a : AF F) : At (evFin F v) (a * b) := by
  intro u hu
  rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u b, hb u hu, mul_zero]

theorem at_add {v : Pl F} {a b : AF F} (ha : At (evFin F v) a) (hb : At (evFin F v) b) :
    At (evFin F v) (a + b) := by
  intro u hu
  rw [smul_add, ha u hu, hb u hu, add_zero]

theorem at_dot {κ : Type} [Fintype κ] {v : Pl F} (a b : κ → AF F) (hb : ∀ i, At (evFin F v) (b i)) :
    At (evFin F v) (a ⬝ᵥ b) := by
  intro u hu
  simp only [dotProduct, Finset.smul_sum]
  exact Finset.sum_eq_zero fun i _ => at_mul (hb i) (a i) u hu

theorem singleFin_one_mul (v : Pl F) (y : Af F) : singleFin v 1 * y = singleFin v (evalV F v y) := by
  refine af_ext fun u => ?_
  rw [map_mul]
  by_cases h : u = v
  · subst h; rw [evalV_singleFin_self, evalV_singleFin_self, one_mul]
  · rw [evalV_singleFin_ne h, evalV_singleFin_ne h, zero_mul]

theorem evFin_inr_singleFin (v : Pl F) (c : Fv F v) :
    evFin F v (LinearMap.inr F (Ainf F) (Af F) (singleFin v c)) = c :=
  evalV_singleFin_self v c

theorem eq_inr_of_at {v : Pl F} {a : AF F} (ha : At (evFin F v) a) :
    a = LinearMap.inr F (Ainf F) (Af F) (singleFin v (evFin F v a)) := by
  have h1 := ha (1 - (show AF F from LinearMap.inr F (Ainf F) (Af F) (singleFin v 1)))
    (by rw [map_sub, map_one, evFin_inr_singleFin, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h1
  refine h1.trans (Prod.ext ?_ ?_)
  · show (0 : Ainf F) * a.1 = 0
    exact zero_mul _
  · show singleFin v 1 * a.2 = singleFin v (evFin F v a)
    exact singleFin_one_mul v a.2

theorem evFin_invOf_two (v : Pl F) : evFin F v (⅟(2 : AF F)) = (2 : Fv F v)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]

end GlobalTheory.VacLine.RhoSlice

namespace GlobalTheory.VacLine.RhoSlice

theorem at_coord {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {v : Pl F} {w : Matrix (Fin n) (Fin d) (AE F E)}
    (hw : At (evFin F v) w) (i : Fin n × Fin d) :
    At (evFin F v) ((M.co.e w).1 i) ∧ At (evFin F v) ((M.co.e w).2 i) := by
  have h : ∀ u : AF F, evFin F v u = 0 → u • M.co.e w = 0 := fun u hu => by
    rw [← LinearEquiv.map_smul, hw u hu, map_zero]
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have := congrArg (fun p => p.1 i) (h u hu)
    simpa using this
  · have := congrArg (fun p => p.2 i) (h u hu)
    simpa using this

theorem rho_slice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F)
    (w : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) w →
    ∀ (Φ : (Fin n × Fin d → AF F) → ℂ) (x : Fin n × Fin d → mixedEmbedding.mixedSpace F),
      slice (M.co.rho ψ w Φ) x = finOp ψ v (locPt v (M.co.e w)) (slice Φ x) := by
  intro F E _ _ _ _ _ σ n d X W M ψ v w hw Φ x
  funext y
  have hc := at_coord M hw
  have hz : At (evFin F v) (mkPt x y ⬝ᵥ (M.co.e w).2 + ⅟(2 : AF F) * ((M.co.e w).1 ⬝ᵥ (M.co.e w).2)) :=
    at_add (at_dot _ _ fun i => (hc i).2) (at_mul (at_dot _ _ fun i => (hc i).2) _)
  show ψ (mkPt x y ⬝ᵥ (M.co.e w).2 + ⅟(2 : AF F) * ((M.co.e w).1 ⬝ᵥ (M.co.e w).2)) * Φ (mkPt x y + (M.co.e w).1) = _
  rw [show ψ (mkPt x y ⬝ᵥ (M.co.e w).2 + ⅟(2 : AF F) * ((M.co.e w).1 ⬝ᵥ (M.co.e w).2)) =
    psiLoc ψ v (evFin F v (mkPt x y ⬝ᵥ (M.co.e w).2 + ⅟(2 : AF F) * ((M.co.e w).1 ⬝ᵥ (M.co.e w).2))) from
    congrArg ψ (eq_inr_of_at hz)]
  unfold finOp slice locPt
  congr 2
  · simp only [dotProduct, map_add, map_mul, map_sum, evFin_invOf_two, evFin_mkPt]
    ring
  · funext i
    show mkPt x y i + (M.co.e w).1 i = _
    rw [eq_inr_of_at (hc i).1]
    exact Prod.ext (add_zero _) rfl

end GlobalTheory.VacLine.RhoSlice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameExtendsToBlockBasisStatement
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_frame_extends_to_block_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E), GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • J.map σ) Xf Yf →
    ∃ (n₀ : ℕ) (Z₀ : Matrix (Fin n) (Fin n₀) E) (Q : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin n) E),
      n₀ + (r₀ + r₀) = n ∧
      Q * Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) = 1 ∧ Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) * Q = 1 ∧
      (Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf))ᵀ * J * (Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf)).map σ =
        Matrix.fromBlocks (Z₀ᵀ * J * Z₀.map σ) 0 0 (Matrix.fromBlocks 0 1 1 0) ∧
      (Z₀ᵀ * J * Z₀.map σ).det ≠ 0 ∧ (∀ i j, σ ((Z₀ᵀ * J * Z₀.map σ) j i) = (Z₀ᵀ * J * Z₀.map σ) i j) ∧
      Formalism.UG.cT (σ : E →+* E) Xf * ((1 : E) • J.map σ) * Z₀ = 0 ∧ Formalism.UG.cT (σ : E →+* E) Yf * ((1 : E) • J.map σ) * Z₀ = 0 := by
  first | exact @GlobalTheory.SiegelSet.PerpBasis.exists_perp_basis | exact GlobalTheory.SiegelSet.PerpBasis.exists_perp_basis | (intros; apply GlobalTheory.SiegelSet.PerpBasis.exists_perp_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameGLTwoDecomposition
section
noncomputable section

namespace GlobalTheory.ThK.GLTwo

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (σ : E →ₐ[F] E) in

def IsHypPlane {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) : Prop :=
  n = n₁ + 2 ∧ form σ Y.J H.x H.x = 0 ∧ form σ Y.J H.y H.y = 0 ∧ form σ Y.J H.x H.y = 1 ∧
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) ∧ H.ιᵀ * Y.J * H.ι.map σ = Y₁.J

theorem IsAdapted.isHypPlane {σ : E →ₐ[F] E} {B : Base F E} {n n₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n}
    {Y₁ : Spc F E n₁} {i₀ i₁ : ℕ} (h : H.IsAdapted σ B Y Y₁ i₀ i₁) : IsHypPlane σ H Y Y₁ :=
  ⟨h.rank, h.xx, h.yy, h.xy, h.orth, h.gram⟩

theorem IsIsoPlane.isHypPlane {σ : E →ₐ[F] E} {B : Base F E} {n n₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n}
    {Y₁ : Spc F E n₁} (h : GlobalTheory.ThK.DescB.IsIsoPlane σ B H Y Y₁) : IsHypPlane σ H Y Y₁ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def IsDiagAt (X Y : Matrix (Fin n) (Fin r) E) (i : Fin r) (t : (AE F E)ˣ) (g : GAd σ J) : Prop :=
  (matHom _ σ J g).1 *ᵥ (fun k => adMat F X k i) = t.1 • (fun k => adMat F X k i) ∧
    (matHom _ σ J g).1 *ᵥ (fun k => adMat F Y k i) = cA σ (t⁻¹).1 • (fun k => adMat F Y k i) ∧
    ∀ z ∈ colPerp σ J X {i} ⊓ colPerp σ J Y {i}, (matHom _ σ J g).1 *ᵥ z = z

def WittFrameGLTwoDecomposition : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (h1 : 1 < r), IsWittFrame σ J X Y →
    ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K → ∀ φ : GAd σ J → ℂ, IsAut σ J K φ →
    (∀ S : Finset (Fin r), ¬ (∀ k ∈ S, ∀ i ≤ k, i ∈ S) → IsCuspComp σ J X Y S K φ 0) →
    ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (χa χb : Chr F E) (ma mb : InfinitePlace F → ℤ),
      HasExp τ χa ma → HasExp τ χb mb → (∃ w, ma w ≠ mb w) →
    ∀ za0 za1 zb1 : ℝ, za0 < zb1 + 1 →
    ∀ c0 : GAd σ J → ℂ, IsConstAlong σ J X {⟨0, by omega⟩} φ c0 →
      (∀ t g, IsDiagAt σ J X Y ⟨0, by omega⟩ t g → ∀ x,
        c0 (g * x) = (χa t : ℂ) * (((absE F E t : ℝ) ^ za0 : ℝ) : ℂ) * c0 x) →
    ∀ c01 : GAd σ J → ℂ, IsConstAlong σ J X {⟨0, by omega⟩, ⟨1, h1⟩} φ c01 →
    ∀ (x : GAd σ J) (A B : ℂ), (∀ t g, IsDiagAt σ J X Y ⟨1, h1⟩ t g →
        c01 (g * x) = A * ((χa t : ℂ) * (((absE F E t : ℝ) ^ za1 : ℝ) : ℂ)) +
          B * ((χb t : ℂ) * (((absE F E t : ℝ) ^ zb1 : ℝ) : ℂ))) → B = 0

end GlobalTheory.ThK.GLTwo

end
end

