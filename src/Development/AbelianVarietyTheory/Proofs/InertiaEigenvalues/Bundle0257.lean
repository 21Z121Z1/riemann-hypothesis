import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0124
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeField
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0186
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0196
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TmulMemFilV
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EmbeddingJump

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mulVdR_tmul (c : K) (v : V) (z : BdR) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (Qp := Qp) c (v ⊗ₜ[Qp] z) =
      v ⊗ₜ[Qp] (algebraMap K BdR c * z) := by
  simp [mulVdR]

theorem act_mul (g : G) (c : K) (x : V ⊗[Qp] BdR) :
    actVdR PD ρ g (mulVdR (K := K) (LL := LL) c x) = mulVdR (K := K) (LL := LL) c (actVdR PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v z => simp [mulVdR, actVdR]

theorem mul_mem_DdR (c : K) {x : V ⊗[Qp] BdR} (hx : x ∈ DdR PD ρ) :
    mulVdR (K := K) (LL := LL) c x ∈ DdR PD ρ := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  rw [act_mul, hx g]

theorem tmul_mem_FilV (a : ℤ) (v : V) {z : BdR} (hz : z ∈ PD.Fil a) :
    v ⊗ₜ[Qp] z ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨v ⊗ₜ[Qp] ⟨z, hz⟩, by simp⟩

theorem mul_mem_FilV (a : ℤ) (c : K) {x : V ⊗[Qp] BdR} (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    mulVdR (K := K) (LL := LL) c x ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨w, rfl⟩ := hx
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add]; exact Submodule.add_mem _ hx hy
  | tmul v z =>
    simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply,
      Submodule.subtype_apply]
    rw [mulVdR_tmul, ← Algebra.smul_def]
    exact tmul_mem_FilV PD a v ((PD.Fil a).smul_mem c z.2)

theorem mul_mul (c c' : K) (x : V ⊗[Qp] BdR) :
    mulVdR (K := K) (LL := LL) c (mulVdR (K := K) (LL := LL) c' x) =
      mulVdR (K := K) (LL := LL) (c * c') x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v z => simp only [mulVdR_tmul, map_mul, mul_assoc]

theorem mul_add' (c c' : K) (x : V ⊗[Qp] BdR) :
    mulVdR (K := K) (LL := LL) (c + c') x =
      mulVdR (K := K) (LL := LL) c x + mulVdR (K := K) (LL := LL) c' x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | tmul v z => simp only [mulVdR_tmul, map_add, add_mul, TensorProduct.tmul_add]

theorem mul_smul' (r : Qp) (c : K) (x : V ⊗[Qp] BdR) :
    mulVdR (K := K) (LL := LL) (r • c) x = r • mulVdR (K := K) (LL := LL) c x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul v z =>
    simp only [mulVdR_tmul]
    rw [← TensorProduct.tmul_smul, ← Algebra.smul_def, ← Algebra.smul_def, smul_assoc]

def projMap (τ : K →ₐ[Qp] LL) (x : V ⊗[Qp] BdR) : K ⊗[Qp] K →ₗ[Qp] V ⊗[Qp] BdR :=
  TensorProduct.lift (LinearMap.mk₂ Qp (fun a c => τ a • mulVdR (K := K) (LL := LL) c x)
    (fun a a' c => by rw [map_add, add_smul])
    (fun r a c => by rw [map_smul, smul_assoc])
    (fun a c c' => by rw [mul_add', smul_add])
    (fun r a c => by rw [mul_smul', smul_comm]))

theorem proj_mem (τ : K →ₐ[Qp] LL) {n : ℕ} (α β : Fin n → K)
    (h : ∀ κ : K, ∑ j, (κ * α j) ⊗ₜ[Qp] β j = ∑ j, α j ⊗ₜ[Qp] (κ * β j)) (u : ℤ)
    {x : V ⊗[Qp] BdR} (hx : x ∈ DdR PD ρ) (hu : x ∈ FilV PD (LL := LL) (V := V) u)
    (hj : ¬ IsJumpV PD ρ τ u) :
    ∑ j, τ (α j) • mulVdR (K := K) (LL := LL) (β j) x ∈ FilV PD (LL := LL) (V := V) (u + 1) := by
  have he : FildR PD ρ τ (u + 1) = FildR PD ρ τ u := not_not.1 hj
  have : ∑ j, τ (α j) • mulVdR (K := K) (LL := LL) (β j) x ∈ FildR PD ρ τ u := by
    refine ⟨⟨Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (mul_mem_DdR PD ρ _ hx), ?_⟩,
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (mul_mem_FilV PD u _ hu)⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    intro c
    have := congrArg (projMap τ x) (h c)
    simp only [map_sum, projMap, TensorProduct.lift.tmul, LinearMap.mk₂_apply] at this
    simp only [map_sum, map_smul, mul_mul, Finset.smul_sum, smul_smul, ← map_mul]
    exact this.symm
  rw [← he] at this
  exact this.2

def coordMap (f : V →ₗ[Qp] Qp) : V ⊗[Qp] BdR →ₗ[Qp] BdR :=
  (TensorProduct.lid Qp BdR).toLinearMap ∘ₗ TensorProduct.map f LinearMap.id

theorem coordMap_mem (f : V →ₗ[Qp] Qp) (a : ℤ) {x : V ⊗[Qp] BdR}
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) : coordMap f x ∈ PD.Fil a := by
  obtain ⟨w, rfl⟩ := hx
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add]; exact Submodule.add_mem _ hx hy
  | tmul v z =>
    simp only [coordMap, TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply,
      Submodule.subtype_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
      LinearEquiv.coe_coe, TensorProduct.lid_tmul]
    exact ((PD.Fil a).restrictScalars Qp).smul_mem _ z.2

theorem coord_proj (τ : K →ₐ[Qp] LL) {n d : ℕ} (α β : Fin n → K) (f : V →ₗ[Qp] Qp)
    (b : Fin d → V) (y : Fin d → BdR) (s : BdR) :
    coordMap f (∑ j, τ (α j) • mulVdR (K := K) (LL := LL) (β j) (∑ k, b k ⊗ₜ[Qp] (y k * s))) =
      (∑ j, ∑ k, (algebraMap K BdR (β j) * algebraMap Qp BdR (f (τ (α j) • b k))) * y k) * s := by
  simp only [map_sum, mulVdR_tmul, Finset.smul_sum, TensorProduct.smul_tmul', coordMap,
    LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul,
    LinearMap.id_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def]
  ring

end General

open GlobalTheory.DeRhamSymbol

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : ThetaL P AI)

theorem theta_sum {ι : Type} (s : Finset ι) (z : ι → P.R.BdR)
    (hz : ∀ i, z i ∈ (P.PD (botExt l)).Fil 0) : J.θ (∑ i ∈ s, z i) = ∑ i ∈ s, J.θ (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (J.θ_ker 0 (Submodule.zero_mem _)).2 (Submodule.zero_mem _)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      J.θ_add _ (hz a) _ (Submodule.sum_mem _ fun i _ => hz i), ih]

theorem theta_lin {n d : ℕ} (c : Fin n → Fin d → Om l) (y : Fin d → P.R.BdR)
    (hy : ∀ k, y k ∈ (P.PD (botExt l)).Fil 0)
    (h : ∑ j, ∑ k, algebraMap (Om l) P.R.BdR (c j k) * y k ∈ (P.PD (botExt l)).Fil 1) :
    ∑ j, ∑ k, ((c j k : Om l) : PadicComplex l) * J.θ (y k) = 0 := by
  have hm : ∀ (c : Om l) (k : Fin d), algebraMap (Om l) P.R.BdR c * y k ∈
      (P.PD (botExt l)).Fil 0 := fun c k => by
    have := (P.PD (botExt l)).Fil_mul _ _ _ _ (om_mem c) (hy k)
    rwa [zero_add] at this
  have h3 := (J.θ_ker _ (Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun k _ => hm _ k)).2 h
  rw [theta_sum J _ _ (fun j => Submodule.sum_mem _ fun k _ => hm _ k)] at h3
  rw [← h3]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [theta_sum J _ _ (fun k => hm _ k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [J.θ_mul _ (om_mem _) _ (hy k), J.θ_Om]

theorem mat_apply {n d : ℕ} (β : Fin n → Om l) (m : Fin n → Fin d → Fin d → ℚ_[l])
    (w : Fin d → PadicComplex l) (i : Fin d) :
    (∑ j, ((β j : Om l) : PadicComplex l) • Matrix.of (fun i k : Fin d =>
      algebraMap ℚ_[l] (PadicComplex l) (m j k i))).mulVec w i =
    ∑ k, ∑ j, ((β j * algebraMap ℚ_[l] (Om l) (m j k i) : Om l) : PadicComplex l) * w k := by
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply,
    Finset.sum_mul, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [UniformSpace.Completion.coe_mul]
  rfl

theorem proj_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (θ : ThetaL P AI) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (d : ℕ) (b : Module.Basis (Fin d) ℚ_[l] T.V) (n : ℕ) (α β : Fin n → ↥K.1), (∀ κ : ↥K.1, ∑ j, (κ * α j) ⊗ₜ[ℚ_[l]] β j = ∑ j, α j ⊗ₜ[ℚ_[l]] (κ * β j)) → ∀ t : (P.R.BdR)ˣ, (t : P.R.BdR) = P.ιB P.tB → ∀ (u : ℤ) (y : Fin d → P.R.BdR), (∀ i, y i ∈ (P.PD K).Fil 0) → ∑ i, b i ⊗ₜ[ℚ_[l]] (y i * ((t ^ u : (P.R.BdR)ˣ) : P.R.BdR)) ∈ DdR (P.PD K) T.ρ → ¬ IsJumpV (P.PD K) T.ρ τ u → (∑ j, ((β j : Om l) : PadicComplex l) • Matrix.of (fun i k : Fin d => algebraMap ℚ_[l] (PadicComplex l) (b.repr (τ (α j) • b k) i))).mulVec (fun i => θ.θ (y i)) = 0 := by
  intro l _ P AI θ K LL T τ d b n α β h t ht u y hy hD hj
  obtain rfl : t = tU P := Units.ext ht
  have hF : ∑ i, b i ⊗ₜ[ℚ_[l]] (y i * ((tU P ^ u : (P.R.BdR)ˣ) : P.R.BdR)) ∈
      FilV (P.PD K) (LL := ↥LL.1) (V := T.V) u := by
    refine Submodule.sum_mem _ fun i _ => tmul_mem_FilV _ _ _ ?_
    have := (P.PD K).Fil_mul _ _ _ _ (hy i) ((mem_iff K u _).2 (zpow_mem θ u))
    rwa [zero_add] at this
  have h1 := proj_mem (P.PD K) T.ρ τ α β h u hD hF hj
  funext i
  have h2 := coordMap_mem (P.PD K) (b.coord i) _ h1
  rw [coord_proj, mem_iff, ← shift_iff θ, mul_left_comm, ← Units.val_mul, ← zpow_add,
    neg_add_cancel, zpow_zero, Units.val_one, mul_one] at h2
  have e : ∀ (j : Fin n) (k : Fin d), algebraMap (↥K.1) P.R.BdR (β j) *
      algebraMap ℚ_[l] P.R.BdR (b.coord i (τ (α j) • b k)) =
      algebraMap (Om l) P.R.BdR ((β j : Om l) *
        algebraMap ℚ_[l] (Om l) (b.repr (τ (α j) • b k) i)) := by
    intro j k
    rw [map_mul, ← IsScalarTower.algebraMap_apply]
    rfl
  simp only [e] at h2
  have h3 := theta_lin θ (fun j k => (β j : Om l) *
    algebraMap ℚ_[l] (Om l) (b.repr (τ (α j) • b k) i)) y (fun k => (mem_iff K 0 _).1 (hy k)) h2
  rw [Finset.sum_comm] at h3
  exact (mat_apply (fun j => (β j : Om l)) (fun j k i => b.repr (τ (α j) • b k) i) _ i).trans h3

end GlobalTheory.EmbeddingJump
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationGammaStableAndSubOneMemPiSmul
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.GamSat

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem γ_smul (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.γ T (a • x) = W.γA W.gam a • W.γ T x := by
  have := W.γD_smul T W.gam (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem γA_π (g : W.Gam) : ∃ u u' : LetA O n, u * u' = 1 ∧ W.γA g letπ = letπ * u := by
  obtain ⟨h0, h1⟩ := W.γ₀_X g
  obtain ⟨u₀, hu₀⟩ := PowerSeries.X_dvd_iff.mpr h0
  have hc : PowerSeries.constantCoeff u₀ = ((W.χΓ g : Oˣ) : O) := by
    rw [← h1, hu₀, PowerSeries.coeff_succ_X_mul]
    simp
  refine ⟨fun _ => u₀, fun _ => PowerSeries.invOfUnit u₀ (W.χΓ g), ?_, ?_⟩
  · funext i
    exact PowerSeries.mul_invOfUnit u₀ _ hc
  · funext i
    simp [LocWach.γA, letγ, letπ, hu₀]

theorem map_γ_mem {T₁ T₂ : LocLat G Qp LL O} (π : LatHom T₁.L T₂.L) :
    ∀ y ∈ (W.N T₁).map (mapA W π), W.γ T₂ y ∈ (W.N T₁).map (mapA W π) := by
  rintro _ ⟨n₁, hn₁, rfl⟩
  refine ⟨W.γD T₁ W.gam n₁, W.N_Γ T₁ W.gam n₁ hn₁, ?_⟩
  change W.map π (W.γD T₁ W.gam n₁) = W.γD T₂ W.gam (W.map π n₁)
  exact W.map_γ π W.gam n₁

theorem pow_smul_γ_mem (T : LocLat G Qp LL O) (P : Submodule (LetA O n) (W.DD T))
    (hP : ∀ y ∈ P, W.γ T y ∈ P) (p k : ℕ) (x : W.DD T)
    (h1 : ((p : LetA O n)) ^ k • x ∈ P) (h2 : (letπ : LetA O n) ^ k • x ∈ P) :
    ((p : LetA O n)) ^ k • W.γ T x ∈ P ∧ (letπ : LetA O n) ^ k • W.γ T x ∈ P := by
  constructor
  · have := hP _ h1
    rw [γ_smul, map_pow, map_natCast] at this
    exact this
  · obtain ⟨u, u', huu, hu⟩ := γA_π W W.gam
    have := P.smul_mem (u' ^ k) (hP _ h2)
    have e : u' ^ k * (letπ * u) ^ k = letπ ^ k := by
      rw [← mul_pow, mul_left_comm, mul_comm u' u, huu, mul_one]
    rw [γ_smul, map_pow, hu, smul_smul, e] at this
    exact this

theorem gam_sat (p : ℕ) (T₁ T₂ : LocLat G Qp LL O) (π : LatHom T₁.L T₂.L) :
    (∀ x ∈ GlobalTheory.NL.Coker.satM p ((W.N T₁).map (mapA W π)) (W.N T₂),
      W.γ T₂ x ∈ GlobalTheory.NL.Coker.satM p ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧
    ∀ x ∈ GlobalTheory.NL.Coker.satM p ((W.N T₁).map (mapA W π)) (W.N T₂),
      W.γ T₂ x - x ∈ (GlobalTheory.NL.Coker.satM p ((W.N T₁).map (mapA W π)) (W.N T₂)).map
        (smulA W T₂ letπ) := by
  set P := (W.N T₁).map (mapA W π) with hPdef
  have hP := map_γ_mem W π
  refine ⟨?_, ?_⟩
  · rintro x ⟨hx, k, h1, h2⟩
    exact ⟨W.N_Γ T₂ W.gam x hx, k, pow_smul_γ_mem W T₂ P hP p k x h1 h2⟩
  · rintro x ⟨hx, k, h1, h2⟩
    obtain ⟨y, hy, hxy⟩ := W.N_π T₂ W.gam x hx
    obtain ⟨n₁, hn₁, hn₁x⟩ := h1
    obtain ⟨m₁, hm₁, hnm⟩ := W.N_π T₁ W.gam n₁ hn₁
    have hγ := pow_smul_γ_mem W T₂ P hP p k x ⟨n₁, hn₁, hn₁x⟩ h2

    have hinj : ∀ z w : W.DD T₂, (letπ : LetA O n) • z = (letπ : LetA O n) • w → z = w := by
      intro z w hzw
      obtain ⟨u, hu⟩ := W.EE_π
      rw [← algebraMap_smul W.EE (letπ : LetA O n) z, ← algebraMap_smul W.EE (letπ : LetA O n) w,
        ← hu] at hzw
      have := congrArg (fun z => ((u⁻¹ : W.EEˣ) : W.EE) • z) hzw
      simpa [smul_smul] using this
    have hly : ((p : LetA O n)) ^ k • y = mapA W π m₁ := by
      apply hinj
      rw [smul_comm, ← hxy, smul_sub, ← LinearMap.map_smul, ← hnm]
      have e1 : W.γD T₂ W.gam (((p : LetA O n)) ^ k • x) = ((p : LetA O n)) ^ k • W.γD T₂ W.gam x := by
        have := γ_smul W T₂ (((p : LetA O n)) ^ k) x
        rw [map_pow, map_natCast] at this
        exact this
      rw [← e1, ← hn₁x]
      change W.γD T₂ W.gam (W.map π n₁) - W.map π n₁ = W.map π (W.γD T₁ W.gam n₁ - n₁)
      rw [map_sub, W.map_γ]
    refine ⟨y, ⟨hy, k + 1, ?_, ?_⟩, ?_⟩
    · rw [pow_succ', mul_smul, hly]
      exact P.smul_mem _ ⟨m₁, hm₁, rfl⟩
    · rw [pow_succ, mul_smul, ← hxy, smul_sub]
      exact P.sub_mem hγ.2 h2
    · change (letπ : LetA O n) • y = _
      rw [← hxy]
      rfl

end Generic

theorem wachSaturation_gamma_stable_and_sub_one_mem_pi_smul : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → (∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), W.γ T₂ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧ ∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), W.γ T₂ x - x ∈ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)).map (smulA W T₂ letπ) := by
  intro D HW F l _ K s LL h W T₁ T₂ π _ _
  exact gam_sat W l T₁ T₂ π

end GlobalTheory.NL.GamSat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeFieldStatement
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField : ∀ (g : ℕ) [Fact g.Prime] (N k s : ℕ) (ψ : AddChar (ZMod g) ℂ), eU g N ψ * eU g N ψ = eU g N ψ ∧ (eU g N ψ).coeff 1 = ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹ ∧ (N = k + 2 * s + 1 → eJ g N k s ψ * eJ g N k s ψ = eJ g N k s ψ ∧ (eJ g N k s ψ).coeff 1 = (g : ℂ) ^ k * ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹) ∧ (k < N → eJ' g N k ψ * eJ' g N k ψ = eJ' g N k ψ ∧ (eJ' g N k ψ).coeff 1 = (g : ℂ) ^ k * ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹) := by
  first | exact @GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField | exact GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField | (intros; apply GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Xstab
section
noncomputable section

namespace GlobalTheory.NL.XStab

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem φpow_γA (k : ℕ) (g : W.Gam) (a : LetA O n) :
    (W.φA ^ k) (W.γA g a) = W.γA g ((W.φA ^ k) a) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', AlgHom.mul_apply, AlgHom.mul_apply, ih, W.φA_γA]

theorem X_dvd_γX (g : W.Gam) : W.X ∣ W.γA g W.X := by
  obtain ⟨c, hc⟩ : (PowerSeries.X : PowerSeries O) ∣ W.γ₀ g PowerSeries.X :=
    PowerSeries.X_dvd_iff.2 (W.γ₀_X g).1
  have h1 : W.γA g letπ = letπ * (fun _ => c) := by
    funext i
    simp [LocWach.γA, letγ, letπ, hc]
  refine ⟨(W.φA ^ (W.s - 1)) (fun _ => c), ?_⟩
  rw [LocWach.X, ← φpow_γA, h1, map_mul]

theorem γD_mem_aN_X (T : LocLat G Qp LL O) (δ : W.Gam) (x : W.DD T) (hx : x ∈ aN W T W.X) :
    W.γD T δ x ∈ aN W T W.X := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨c, hc⟩ := X_dvd_γX W δ
  refine ⟨c • W.γD T δ y, (W.N T).smul_mem _ (W.N_Γ T δ y hy), ?_⟩
  change W.X • c • W.γD T δ y = W.γD T δ (W.X • y)
  rw [γD_smulA, hc, mul_smul]

end Generic

theorem xstab : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (δ : ((HW l).W K s LL h).Gam) (x : ((HW l).W K s LL h).DD T), x ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X → ((HW l).W K s LL h).γD T δ x ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X :=
  fun _ HW l _ K s LL h T δ x hx => γD_mem_aN_X ((HW l).W K s LL h) T δ x hx

end GlobalTheory.NL.XStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZetaMemPowInvPhiModuleLattice
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.ZetaDenominator

theorem zetaBound : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.ZetaBound := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ N η H Sig U hA D hT y' hy' m hm hMon
  haveI : CompleteSpace K := by
    haveI := TameDescentExponentData.finite (K := K) (l := l) (e := e) (a := a)
    exact FiniteDimensional.complete ℚ_[l] K
  have hl : l.Prime := Fact.out
  have ha : 1 ≤ a := NeZero.one_le
  obtain ⟨hr1, hrN, hrper⟩ := GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a hl ha (TameDescentExponentData.succ_eq (K := K)) Sig N
    hA.frob_mem hA.zero_mem_Sig hA.card_Sig hA.two_le
  obtain ⟨-, n2, n3, -, -, n6⟩ := GlobalTheory.T.numerical_conditions_theorem_T_large_prime l H N η (maxPeriod l Sig) hA.two_le hA.one_le hA.lt hrN hA.large
  have hl2 : l ≠ 2 := by have := hA.lt; have := hA.one_le; omega
  have hφm := GlobalTheory.T.prime_pow_smul_descent_phi_mem_lattice_of_orbit_bound O K l e a ι η H D (maxPeriod l Sig) hr1
    (fun τ c hc => hrper c (hT.chars_subset τ hc)) n6 hl2 m hm
  obtain ⟨P0, hP0, F0, hF0, hQF, hdec⟩ := GlobalTheory.T.breuilKisin_lpow_eisensteinPow_twisted_decomp O K l e a ι η H D (η * (maxPeriod l Sig + 1)) hA.one_le hA.lt
    (by have := hA.one_le; omega) (by omega) y' hy' m hm hφm
  show (l : K) ^ (η * (maxPeriod l Sig + 1)) • D.zeta (y' + D.phi m) ∈ D.MM
  set c₁ := η * (maxPeriod l Sig + 1)
  set y := y' + D.phi m
  set w := E K l e • D.zeta y - D.EN y with hw_def
  have hw : w ∈ D.Man := by
    have h : D.EN y - E K l e • D.zeta y ∈ D.Man := (D.cls_eq_zero_iff).1 (by rw [← PhiMod.Mon_apply]; exact hMon)
    have := D.Man.neg_mem h
    rwa [neg_sub] at this
  obtain ⟨c, hc, hcE⟩ := exists_mul_frob_E (O := O) (K := K) l e
  have hζ : D.zeta y = c • D.phi w := by
    have h1 : w = E K l e • (D.zeta y - D.conn y) := by simp only [hw_def, PhiMod.EN_apply, smul_sub]
    rw [h1, PhiMod.phi_smul, smul_smul, hcE]
    conv_lhs => rw [PhiMod.zeta_eq, PhiMod.lphi_apply]
    simp only [Nat.cast_smul_eq_nsmul]
  have hE1 : E K l e ^ (2 * H) * Ezpow K l e (-(2 * H : ℤ)) = 1 := by
    have := E_pow_mul_Ezpow_neg (K := K) l e (2 * H)
    push_cast at this
    exact this
  set Q := Ezpow K l e (-(2 * H : ℤ)) • (((l : K) ^ (3 * H))⁻¹ • F0) with hQ_def
  set X0 := Ezpow K l e (-(2 * H : ℤ)) • P0 with hX0_def
  have hsplit : (l : K) ^ c₁ • w = X0 + Q := by
    have h : (l : K) ^ c₁ • w = Ezpow K l e (-(2 * H : ℤ)) • (E K l e ^ (2 * H) • ((l : K) ^ c₁ • w)) := by
      rw [smul_smul, mul_comm, hE1, one_smul]
    rw [h, smul_comm (E K l e ^ (2 * H)) ((l : K) ^ c₁) w, hdec, smul_add]
  have hQ : Q ∈ D.Man := by
    rw [hQ_def, smul_comm]
    exact D.Man.smul_mem _ hQF
  have hX0 : X0 ∈ D.Man := by
    have : X0 = (l : K) ^ c₁ • w - Q := by rw [hsplit, add_sub_cancel_right]
    rw [this]
    exact D.Man.sub_mem (D.Man.smul_mem _ hw) hQ
  have hX0E : X0 ∈ D.EM (2 * H + η) := by
    rw [mem_divE, hX0_def, smul_smul, pow_add, mul_right_comm, hE1, one_mul]
    exact D.upper _ hP0
  have hX0M : X0 ∈ D.M := PhiMod.mem_M_of_mem_Man _ hX0E hX0
  have hφX0 : D.phi X0 ∈ D.MM := PhiMod.ext_mono _ (A_le_S l e) (D.phi_mem_L hX0M)
  obtain ⟨v', hv', hv'eq⟩ := GlobalTheory.T.prime_pow_smul_phi_mem_lattice_of_mem_filtration O K l e a ι η H D (10 * H) (by omega) F0 hF0
  have hl0 : (l : K) ≠ 0 := l_ne_zero (K := K) l
  have hF : D.phi F0 = (l : K) ^ (3 * H) • ((l : K) ^ (2 * H) • ((l : K) ^ (5 * H - η) • v')) := by
    apply smul_right_injective _ (pow_ne_zero η hl0)
    rw [show 10 * H = η + (3 * H + (2 * H + (5 * H - η))) by have := hA.lt; omega] at hv'eq
    simpa only [pow_add, mul_smul] using hv'eq
  have hfr : (l : K⟦X⟧) ^ (2 * H) * frob K l (Ezpow K l e (-(2 * H : ℤ))) = c ^ (2 * H) := by
    rw [← hcE, mul_pow, ← map_pow, mul_assoc, ← map_mul, hE1, map_one, mul_one]
  have hcast : ∀ (n : ℕ) (x : Vec K a ι), (l : K) ^ n • x = (l : K⟦X⟧) ^ n • x := by
    intro n x
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have hφQ' : D.phi Q = c ^ (2 * H) • ((l : K) ^ (5 * H - η) • v') := by
    rw [hQ_def, PhiMod.phi_smul, map_smul, hF, inv_smul_smul₀ (pow_ne_zero _ hl0), hcast (2 * H), smul_smul, mul_comm (frob K l _), hfr]
  have hφQ : D.phi Q ∈ D.MM := by
    rw [hφQ']
    refine D.MM.smul_mem ⟨c ^ (2 * H), pow_mem hc _⟩ ?_
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hv' _
  have key : (l : K) ^ c₁ • D.zeta y = c • (D.phi X0 + D.phi Q) := by
    rw [← map_add, ← hsplit, map_smul, hζ, smul_comm]
  rw [key]
  exact D.MM.smul_mem ⟨c, hc⟩ (add_mem hφX0 hφQ)

end GlobalTheory.ZetaDenominator
end

