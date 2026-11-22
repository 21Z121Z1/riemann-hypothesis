import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0066
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SymmetricMeasureL2NormEqResolutionL2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFinPartMat
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.LevelOpen

theorem exists_cut {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (e : A)
    (he : e * e = e) (hσ : σ e = e) (g : GL (Fin n) A) (hg : g ∈ Formalism.UG.UJ σ J) :
    ∃ k ∈ Formalism.UG.UJ σ J, k.1 = e • g.1 + (1 - e) • (1 : Matrix (Fin n) (Fin n) A) := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, h1, one_mul, sub_zero]
  have key : ∀ X Y Z W : Matrix (Fin n) (Fin n) A,
      (e • X + (1 - e) • Z) * (e • Y + (1 - e) • W) = e • (X * Y) + (1 - e) • (Z * W) := by
    intro X Y Z W
    simp only [add_mul, mul_add, smul_mul_smul_comm, he, h1, h2, h3, zero_smul, add_zero, zero_add]
  have one : ∀ X : Matrix (Fin n) (Fin n) A, e • X + (1 - e) • X = X := by
    intro X; rw [← add_smul, add_sub_cancel, one_smul]
  refine ⟨⟨e • g.1 + (1 - e) • 1, e • (g⁻¹).1 + (1 - e) • 1, ?_, ?_⟩, ?_, rfl⟩
  · rw [key, Units.mul_inv, one_mul, one]
  · rw [key, Units.inv_mul, one_mul, one]
  · have hg' : Formalism.UG.cT σ g.1 * J * g.1 = J := hg
    change Formalism.UG.cT σ (e • g.1 + (1 - e) • 1) * J * (e • g.1 + (1 - e) • 1) = J
    have hc : Formalism.UG.cT σ (e • g.1 + (1 - e) • (1 : Matrix (Fin n) (Fin n) A)) =
        e • Formalism.UG.cT σ g.1 + (1 - e) • 1 := by
      ext i j
      by_cases h : i = j
      · subst h; simp [Formalism.UG.cT, hσ]
      · simp [Formalism.UG.cT, hσ, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
    rw [hc]
    conv_lhs => rw [← one J]
    rw [key, key, hg', one_mul, mul_one, one]

theorem congr_mem_nhds (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (N : ℕ) (hN : 0 < N) :
    {m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) | ∀ z ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec z - z = N • y} ∈
      𝓝 (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) := by
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  have ho : IsOpen {z : Fin n → Af F ⊗[F] E | ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), z = N • y} :=
    (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat F E n L hL).1 N hN
  have hfz : (L.restrictScalars ℤ).FG := by
    have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hfg
    have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
    exact (Module.Finite.iff_fg (N := L.restrictScalars ℤ)).mp (inferInstanceAs (Module.Finite ℤ L))
  obtain ⟨s, hs⟩ := hfz
  have hev : ∀ᶠ m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) in 𝓝 1, ∀ x ∈ s,
      ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
        m.mulVec (GlobalTheory.AdLat.fv F x) - GlobalTheory.AdLat.fv F x = N • y := by
    rw [Filter.eventually_all_finset]
    intro x _
    have hc : Continuous fun m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) =>
        m.mulVec (GlobalTheory.AdLat.fv F x) - GlobalTheory.AdLat.fv F x :=
      (continuous_id.matrix_mulVec continuous_const).sub continuous_const
    exact (ho.preimage hc).mem_nhds ⟨0, zero_mem _, by simp⟩
  refine Filter.mem_of_superset hev fun m hm => ?_
  have hsm : ∀ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) →
      ∀ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), a • y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
    intro a ha y hy
    induction hy using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb, x, hx, rfl⟩ := hx
      exact AddSubgroup.subset_closure ⟨a * b, fun v => mul_mem (ha v) (hb v), x, hx, rfl⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  have hadd : ∀ z w : Fin n → Af F ⊗[F] E,
      (∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec z - z = N • y) →
      (∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec w - w = N • y) →
      ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec (z + w) - (z + w) = N • y := by
    rintro z w ⟨y, hy, h⟩ ⟨y', hy', h'⟩
    exact ⟨y + y', add_mem hy hy', by rw [smul_add, ← h, ← h', Matrix.mulVec_add]; abel⟩
  have hx : ∀ x ∈ Submodule.span ℤ (s : Set (Fin n → E)), ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      m.mulVec (GlobalTheory.AdLat.fv F x) - GlobalTheory.AdLat.fv F x = N • y := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hm x hx
    | zero =>
      have : GlobalTheory.AdLat.fv F (0 : Fin n → E) = 0 := funext fun i => TensorProduct.tmul_zero _ _
      exact ⟨0, zero_mem _, by simp [this]⟩
    | add x y _ _ hx hy =>
      have : GlobalTheory.AdLat.fv F (x + y) = GlobalTheory.AdLat.fv F x + GlobalTheory.AdLat.fv F y :=
        funext fun i => TensorProduct.tmul_add _ _ _
      rw [this]; exact hadd _ _ hx hy
    | smul c x _ hx =>
      obtain ⟨y, hy, h⟩ := hx
      have : GlobalTheory.AdLat.fv F (c • x) = c • GlobalTheory.AdLat.fv F x :=
        funext fun i => map_zsmul (TensorProduct.mk F (Af F) E 1) c (x i)
      refine ⟨c • y, zsmul_mem hy c, ?_⟩
      rw [this, Matrix.mulVec_smul, ← smul_sub, h, smul_comm]
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hxL, rfl⟩ := hz
    obtain ⟨y, hy, h⟩ := hx x (by rw [hs]; exact hxL)
    have : (fun i => a ⊗ₜ[F] x i) = a • GlobalTheory.AdLat.fv F x := by
      funext i
      simp [GlobalTheory.AdLat.fv, TensorProduct.smul_tmul']
    refine ⟨a • y, hsm a ha y hy, ?_⟩
    rw [this, Matrix.mulVec_smul, ← smul_sub, h, smul_comm]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add z w _ _ hz hw => exact hadd z w hz hw
  | neg z _ hz =>
    obtain ⟨y, hy, h⟩ := hz
    exact ⟨-y, neg_mem hy, by rw [smul_neg, ← h, Matrix.mulVec_neg]; abel⟩

theorem continuous_fin (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    Continuous (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) : AF F ⊗[F] E → Af F ⊗[F] E) := by
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  have : ContinuousSMul (Af F) (Af F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  let φ : AF F ⊗[F] E →ₛₗ[(sndA F).toRingHom] Af F ⊗[F] E :=
    { toFun := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)
      map_add' := map_add _
      map_smul' := fun a x => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        rfl }
  have hs : Continuous ((sndA F).toRingHom : AF F → Af F) := continuous_snd
  exact IsModuleTopology.continuous_of_linearMapₛₗ hs φ

theorem exists_finPart_mat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) (AF F ⊗[F] E)) (hg : g ∈ HR (AF F) σ J) :
    ∃ k ∈ HR (AF F) σ J, Formalism.UG.bc (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom k = 1 ∧
      Formalism.UG.bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom k =
        Formalism.UG.bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom g := by
  let e : AF F ⊗[F] E := pairA F 0 1 ⊗ₜ 1
  have he : e * e = e := by
    simp only [e, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1
    exact Prod.ext (mul_zero _) (mul_one _)
  have hσ : sigR (AF F) σ e = e := by
    simp [e, sigR]
  obtain ⟨k, hk, hke⟩ := exists_cut _ (JR (AF F) J) e he hσ g hg
  have h0 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) e = 0 :=
    TensorProduct.zero_tmul _ _
  have h1 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) e = 1 := rfl
  refine ⟨k, hk, Units.ext ?_, Units.ext ?_⟩
  · change k.1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1
    ext i j
    rw [hke]
    by_cases h : i = j
    · subst h; simp [h0]
    · simp [h0, Matrix.one_apply_ne h]
  · ext i j
    change Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (k.1 i j) =
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (g.1 i j)
    rw [hke]
    simp [h1]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_finPart (D : D7) (V : HSp D) (g : GA D V) : ∃ k ∈ GfC V, finHom V k = finHom V g := by
  let g' : HR (AF D.host.F) D.sp.cm.sig V.gram := g
  obtain ⟨k, hk, h1, h2⟩ := exists_finPart_mat D.sp.cm.sig V.gram (matHom V g) g'.2
  let k' : HR (AF D.host.F) D.sp.cm.sig V.gram := ⟨k, hk⟩
  exact ⟨k', h1, h2⟩

theorem level_mem_nhds : ∀ (D : D7) (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)), 0 < N → IsLevelK V N Kf → ∀ g₀ : GA D V, {g : GA D V | ∃ k ∈ Kf, ∃ h ∈ GinfC V, g = g₀ * k * h} ∈ 𝓝 g₀ := by
  intro D V N Kf hN hK g₀
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  let ψ : V.V →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
    V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E)
  let L := V.L0.map ψ
  have hfg : L.FG := V.standardTuple_isLattice.fg.map ψ
  have hL : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have : (L : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' V.L0 := rfl
    rw [this, ← Submodule.map_span, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]
  have hhat : GlobalTheory.AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) = latHat V := by
    unfold GlobalTheory.AdLat.hat latHat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
  have hn := congr_mem_nhds D.host.F D.host.E V.rank L hfg hL N hN
  rw [hhat] at hn
  have hm : Continuous fun g : GA D V => (matHom V g).1 :=
    Units.continuous_val.comp continuous_subtype_val
  have hf : Continuous fun g : GA D V => (finHom V g).1 := hm.matrix_map (continuous_fin D.host.F D.host.E)
  have hc : Continuous fun g : GA D V => (finHom V (g₀⁻¹ * g)).1 := hf.comp (continuous_const_mul g₀⁻¹)
  have h1 := hc.continuousAt.preimage_mem_nhds (x := g₀) (by rw [inv_mul_cancel, map_one]; exact hn)
  refine Filter.mem_of_superset h1 fun g hg => ?_
  obtain ⟨k, hk, hkg⟩ := exists_finPart D V (g₀⁻¹ * g)
  refine ⟨k, (hK k).mpr ⟨hk, by rw [hkg]; exact hg⟩, k⁻¹ * (g₀⁻¹ * g), ?_, by group⟩
  change finHom V _ = 1
  rw [map_mul, map_inv, hkg, inv_mul_cancel]

end GlobalTheory.LevelOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelSubgroup
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem det_gram_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) :
    S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have hy : S.frame.equivFun.symm v = 0 := by
    apply S.nondeg.2
    intro x
    have hi : ∀ i, S.hT (S.frame i) (S.frame.equivFun.symm v) = 0 := by
      intro i
      have := congrFun h0 i
      rw [Module.Basis.equivFun_symm_apply, map_sum]
      simpa [Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, mul_comm] using this
    rw [← S.frame.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hi, smul_zero]
  exact S.frame.equivFun.symm.map_eq_zero_iff.1 hy

theorem det_mul_sigR_det {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) (g : GL (Fin M) (R ⊗[F] E))
    (hg : g ∈ HR R σ J) : g.1.det * sigR R σ g.1.det = 1 := by
  have h : Formalism.UG.cT (sigR R σ) g.1 * JR R J * g.1 = JR R J := hg
  have h2 := congrArg Matrix.det h
  have hu : IsUnit (JR (F := F) R J).det := by
    have : (JR (F := F) R J).det = inclR (F := F) R J.det := ((inclR (F := F) R).map_det J).symm
    rw [this]
    exact (IsUnit.mk0 _ hJ).map _
  have h3 : (Formalism.UG.cT (sigR R σ) g.1).det = sigR R σ g.1.det := by
    rw [Formalism.UG.cT, Matrix.det_transpose]
    exact ((sigR R σ).map_det g.1).symm
  rw [Matrix.det_mul, Matrix.det_mul, h3] at h2
  apply hu.mul_left_cancel
  linear_combination h2

theorem det_finHom_norm {D : D7} (V : HSp D) (k : GA D V) :
    (finHom V k).1.det * sigR (Af D.host.F) D.sp.cm.sig (finHom V k).1.det = 1 := by
  have h := det_mul_sigR_det (AF D.host.F) D.sp.cm.sig V.gram (det_gram_ne_zero V) (matHom V k) k.2
  let φ := (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have e : (finHom V k).1.det = φ (matHom V k).1.det := (φ.map_det _).symm
  have c : ∀ x, sigR (Af D.host.F) D.sp.cm.sig (φ x) = φ (sigR (AF D.host.F) D.sp.cm.sig x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [φ, sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [e, c, ← map_mul, h, map_one]

theorem finHom_inv_mulVec_mem {D : D7} (V : HSp D) (k : GA D V)
    (hk : ∀ z ∈ latHat V, (finHom V k).1.mulVec z ∈ latHat V) :
    ∀ z ∈ latHat V, (finHom V k⁻¹).1.mulVec z ∈ latHat V := by
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
    V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))
  have hL : latHat V = GlobalTheory.AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) := by
    unfold Formalism.L2.Pj.latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  have hfg : L.FG := V.standardTuple_isLattice.fg.map _
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have : (L : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
    rw [this, Submodule.span_image, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofBijective D.sp.cm.sig (D.sp.cm.sig.bijective)
  rw [hL] at hk ⊢
  rw [map_inv]
  exact GlobalTheory.AdLat.inv_mulVec_mem_hat _ _ _ L (finHom V k) c hfg hsp hk (det_finHom_norm V k)

theorem exists_level_subgroup {G A : Type} [Group G] [CommRing A] {n : ℕ} (f : G →* GL (Fin n) A) (H : Subgroup G)
    (Λ : AddSubgroup (Fin n → A)) (N : ℕ)
    (hinv : ∀ k : G, (∀ z ∈ Λ, (f k).1.mulVec z ∈ Λ) → ∀ z ∈ Λ, (f k⁻¹).1.mulVec z ∈ Λ) :
    ∃ K : Subgroup G, (∀ k, k ∈ K ↔ k ∈ H ∧ ∀ z ∈ Λ, ∃ y ∈ Λ, (f k).1.mulVec z - z = N • y) ∧
      ∀ k ∈ K, (f k).1.mulVec '' (Λ : Set (Fin n → A)) = Λ := by
  have hin : ∀ k : G, (∀ z ∈ Λ, ∃ y ∈ Λ, (f k).1.mulVec z - z = N • y) →
      ∀ z ∈ Λ, (f k).1.mulVec z ∈ Λ := by
    intro k hk z hz
    obtain ⟨y, hy, e⟩ := hk z hz
    rw [sub_eq_iff_eq_add.1 e]
    exact add_mem (nsmul_mem hy N) hz
  have hmul : ∀ (a b : G) z, (f (a * b)).1.mulVec z = (f a).1.mulVec ((f b).1.mulVec z) := by
    intro a b z
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hone : ∀ z, (f 1).1.mulVec z = z := by
    intro z
    rw [map_one, Units.val_one, Matrix.one_mulVec]
  refine ⟨{ carrier := {k | k ∈ H ∧ ∀ z ∈ Λ, ∃ y ∈ Λ, (f k).1.mulVec z - z = N • y}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun k => Iff.rfl, ?_⟩
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun z hz => ?_⟩
    obtain ⟨y, hy, e⟩ := hb' z hz
    obtain ⟨y', hy', e'⟩ := ha' _ (hin b hb' z hz)
    refine ⟨y' + y, add_mem hy' hy, ?_⟩
    rw [hmul, nsmul_add, ← e, ← e']
    abel
  · exact ⟨one_mem _, fun z _ => ⟨0, zero_mem _, by rw [hone, sub_self, nsmul_zero]⟩⟩
  · rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun z hz => ?_⟩
    obtain ⟨y, hy, e⟩ := ha' _ (hinv a (hin a ha') z hz)
    refine ⟨-y, neg_mem hy, ?_⟩
    rw [← hmul, mul_inv_cancel, hone] at e
    rw [neg_nsmul, ← e, neg_sub]
  · rintro k ⟨-, hk⟩
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hin k hk z hz
    · intro z hz
      exact ⟨_, hinv k (hin k hk) z hz, (hmul k k⁻¹ z).symm.trans (by rw [mul_inv_cancel, hone])⟩

theorem exists_isLevelK : ∀ (D : D7) (V : HSp D) (N : ℕ), ∃ Kf : Subgroup (GA D V), IsLevelK V N Kf ∧ ∀ k ∈ Kf, (finHom V k).1.mulVec '' (latHat V : Set _) = latHat V :=
  fun _ V N => exists_level_subgroup (finHom V) (GfC V) (latHat V) N (finHom_inv_mulVec_mem V)

end GlobalTheory.RecDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelGoodAndSign
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

theorem level_good_and_sign : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ p : ℕ, p.Prime → Q.l.GoodAt p) ∧ Q.l.A = 1 ∧ ∀ τ : D.host.E →+* ℂ, τ (Q.H.rt : D.host.E) = Q.H.rt0 → (τ (-D.host.xi0)).im < 0 := by
  rintro D Q ⟨⟨-, hrt, hrt0, -⟩, ⟨hM, hA⟩, -, -⟩
  refine ⟨fun p hp => ?_, hA, fun τ hτ => ?_⟩
  · have hodd := Q.l.odd
    rw [hM] at hodd
    have h3 : ∀ a : ℕ, a.Prime → Odd a → 3 ≤ a := fun a ha ho => by
      have h2 := ha.two_le
      obtain ⟨k, hk⟩ := ho
      omega
    have ha := h3 _ (D.host.g_prime 0) (Nat.Odd.of_mul_left hodd)
    have hb := h3 _ (D.host.g_prime 1) (Nat.Odd.of_mul_right hodd)
    have hab : (D.host.g 0).Coprime (D.host.g 1) :=
      (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.GoodAt
    have hM0 : Q.l.M ≠ 0 := by have := Q.l.three_le; omega
    have key : ∀ c, 3 ≤ c → c ∣ Q.l.M → ¬ p ∣ c → 3 ≤ Q.l.M / p ^ Q.l.M.factorization p :=
      fun c hc hd hn => hc.trans (Nat.le_of_dvd (Nat.ordCompl_pos p hM0) (Nat.dvd_ordCompl_of_dvd_not_dvd hd hn))
    by_cases h : p ∣ D.host.g 0
    · refine key _ hb (hM ▸ dvd_mul_left _ _) fun h' => hp.one_lt.ne' ?_
      exact Nat.eq_one_of_dvd_coprimes hab h h'
    · exact key _ ha (hM ▸ dvd_mul_right _ _) h
  · rw [hrt, hrt0] at hτ
    have h1 := xi0_embedding_im_pos D τ ((mem_cm_type_iff D τ).2 hτ)
    have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    have hpos : 0 < (D.host.φ₀ D.host.sqrtMinusD).im := by
      rw [hφ]
      have hd : (0 : ℝ) < D.host.d := by exact_mod_cast d_pos D
      simpa using hd
    rw [if_pos hpos, Int.cast_one, _root_.one_mul] at h1
    rw [map_neg, Complex.neg_im]
    linarith

end GlobalTheory.RecDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NonemptyFrPtComplex
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem nonempty_frPt_complex : N1c → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ σ : c.F →+* ℂ, Nonempty (FrPt Xo c (CAt σ)) := by
  intro hN hT E _ _ _ H Dw l Xo c h σ
  classical
  obtain ⟨L, _, _, j, x, hx⟩ := GlobalTheory.T.xoNumPt_of_p_add_q_pos hN E H Dw l Xo c h
  let _ : Algebra c.F L := j.toAlgebra
  let _ : Algebra c.F ℂ := σ.toAlgebra
  have : Algebra.IsAlgebraic c.F L := by
    have : IsScalarTower ℚ c.F L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    exact Algebra.IsAlgebraic.tower_top (K := ℚ) c.F
  let φ : L →ₐ[c.F] ℂ := IsAlgClosed.lift
  let _ : Algebra L ℂ := φ.toRingHom.toAlgebra
  obtain ⟨_, y, _⟩ := gfp_frPt_gen (Xo := Xo) (c := c) (L := L) (L' := ℂ) hT
    (fun r => (φ.commutes r).symm) x hx (fun τ i j => if i = j then 1 else 0)
    (fun τ i => by simp) (fun τ i j hij => by simp [hij.ne'])
  exact ⟨y⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ParOfTraceOne
section
noncomputable section

namespace GlobalTheory.TorusFrameRigid

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E]

def hfR (ι : Type) [Fintype ι] : EuclideanSpace ℂ ι →ₗ[ℝ] EuclideanSpace ℂ ι →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ Hf
    (fun u v w => by simp [Hf, add_mul, Finset.sum_add_distrib])
    (fun c u v => by simp [Hf, Finset.mul_sum, mul_assoc])
    (fun u v w => by simp [Hf, mul_add, Finset.sum_add_distrib])
    (fun c u v => by simp [Hf, Finset.mul_sum, mul_left_comm])

def actR (dim : (E →+* ℂ) → ℕ) (α : 𝓞 E) : Vsp dim →ₗ[ℝ] Vsp dim where
  toFun := act α
  map_add' := GlobalTheory.TupleSumPos.act_add_vec α
  map_smul' c v := by ext i; simp [act, mul_left_comm]

structure Match (Y Y' : PT E) (ψ : Vsp Y.dim ≃ₗ[ℝ] Vsp Y'.dim) : Prop where
  lat : ∀ y, y ∈ Y.L ↔ ψ y ∈ Y'.L
  act : ∀ α y, ψ (act α y) = act α (ψ y)
  herm : (∀ u v, Hf (ψ u) (ψ v) = Hf u v) ∨ ∀ u v, Hf (ψ u) (ψ v) = conj (Hf u v)

variable {Y Y' : PT E} {ψ : Vsp Y.dim ≃ₗ[ℝ] Vsp Y'.dim}

variable [IsCMField E] {r : ℕ} {X : Data E r} {x : Frame X.Ψ r}

open GlobalTheory.SemicharIndep

def EpsBy (Y : PT E) (w : 𝓞 E) : Prop := ∀ y ∈ Y.L, (Y.eps y : ℝ) = Real.cos (Real.pi * (Hf y (act w y)).im)

omit [IsCMField E] in
theorem Match.eps (h : Match Y Y' ψ) {w : 𝓞 E} (he : EpsBy Y w) (he' : EpsBy Y' w) :
    ∀ y ∈ Y.L, Y'.eps (ψ y) = Y.eps y := fun y hy => by
  have : (Y'.eps (ψ y) : ℝ) = Y.eps y := by
    rw [he y hy, he' _ ((h.lat y).1 hy), ← h.act]
    rcases h.herm with h1 | h1 <;> simp [h1]
  exact_mod_cast this

end GlobalTheory.TorusFrameRigid
end
end

