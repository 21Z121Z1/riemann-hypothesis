import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1721
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1849
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CocycleTrivialOnProjectiveCover
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenIntertwinerModels
section
noncomputable section

namespace GlobalTheory.ThK.ModelPol

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def finPr {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : (κ → Af F) → ℂ :=
  fun y => ∏ᶠ v, φ v fun i => evalV F v (y i)

theorem pure_eq {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    pure f φ = pureA F f (finPr φ) := rfl

theorem finPr_mem {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) : finPr φ ∈ SB _ :=
  ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hSB hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd⟩

theorem exists_finPr_ne {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) : ∃ y, finPr φ y ≠ 0 := by
  have key : ∀ v : Pl F, ∃ p : κ → Fv F v, φ v p ≠ 0 ∧
      (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 → ∀ i, p i ∈ v.adicCompletionIntegers F) := by
    intro v
    obtain ⟨p, hp⟩ := Function.ne_iff.1 (h0 v)
    refine ⟨p, hp, fun h => ?_⟩
    rw [h] at hp
    exact Set.mem_of_indicator_ne_zero hp
  choose p hp hp' using key
  refine ⟨fun i => ⟨fun v => p v i, ?_⟩, ?_⟩
  · filter_upwards [hstd] with v hv using hp' v hv i
  · exact finprod_induction (fun z : ℂ => z ≠ 0) one_ne_zero (fun a b ha hb => mul_ne_zero ha hb) fun v => hp v

def pt {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)

open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain MeasureTheory Filter Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.ThK.ModelPol.pureA_pt {κ : Type}
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) :
    _root_.GlobalTheory.WeilM.pureA F f g (_root_.GlobalTheory.ThK.ModelPol.pt x y) = f x * g y := by
  unfold _root_.GlobalTheory.WeilM.pureA _root_.GlobalTheory.ThK.ModelPol.pt
  simp

open scoped Classical in

theorem proj_adm {κ : Type} [Fintype κ] (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) :
    (LinearMap.proj (pt x y) : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g y • (BoundedContinuousFunction.evalCLM ℂ x).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ), fun f => ?_⟩
  rw [LinearMap.proj_apply, pureA_pt]
  simp [mul_comm]

section

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem pol_map (M M' : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (D D' : Matrix (Fin n) (Fin d) (AE F E) → SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d))
    (hD : ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ ↔ f₁ = D u f)
    (hD' : ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M'.heisLine ψ u) f f₁ ↔ f₁ = D' u f)
    (ei : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) (hb : Function.Bijective ei)
    (hi : ∀ u, At (evI F) u → ∀ f, ei (D u f) = D' u (ei f)) : (M.Pol ψ τ).map ei = M'.Pol ψ τ := by
  have hG : ∀ f, M.IsGauss ψ τ f ↔ M'.IsGauss ψ τ (ei f) := fun f => by
    refine exists_congr fun ε => forall₂_congr fun u u' => forall₃_congr fun hu hu' _ => ⟨fun h g g' hg hg' => ?_, fun h g g' hg hg' => ?_⟩
    · rw [(hD' u hu _ _).1 hg, (hD' u' hu' _ _).1 hg', ← hi u hu, ← hi u' hu',
        h _ _ ((hD u hu _ _).2 rfl) ((hD u' hu' _ _).2 rfl), map_smul]
    · apply hb.1
      rw [(hD u hu _ _).1 hg, (hD u' hu' _ _).1 hg', map_smul, hi u hu, hi u' hu']
      exact h _ _ ((hD' u hu _ _).2 rfl) ((hD' u' hu' _ _).2 rfl)
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    refine sInf_le ⟨fun f hf => ?_, fun u hu f hf f₁ h₁ => ?_⟩
    · exact Submodule.mem_sInf.2 fun N hN => hN.1 _ ((hG f).1 hf)
    · refine Submodule.mem_sInf.2 fun N hN => hN.2 u hu (ei f) (Submodule.mem_sInf.1 hf N hN) _ ?_
      rw [hD' u hu, (hD u hu _ _).1 h₁, hi u hu]
  · refine sInf_le ⟨fun g hg => ?_, ?_⟩
    · obtain ⟨f, rfl⟩ := hb.2 g
      exact Submodule.mem_map_of_mem (Submodule.mem_sInf.2 fun N hN => hN.1 _ ((hG f).2 hg))
    · rintro u hu _ ⟨f, hf, rfl⟩ g₁ h₁
      rw [(hD' u hu _ _).1 h₁, ← hi u hu]
      exact Submodule.mem_map_of_mem (Submodule.mem_sInf.2 fun N hN =>
        hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) _ ((hD u hu _ _).2 rfl))

theorem actsD_iff (hA : GlobalTheory.RealLift.ActsLaws) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (AE F E))
    (f g : SInf F (Fin n × Fin d)) (h : GlobalTheory.RealLift.SD (fun t => M.co.rho ψ (realAd F t • u)) f g) (f₁ : SInf F (Fin n × Fin d)) :
    ActsD (evI F) (M.heisLine ψ u) f f₁ ↔ f₁ = g := by
  have h1 : ActsD (evI F) (M.heisLine ψ u) f g := (hA F _ f g g).1 _ (fun t => by
    funext x; simp [Model.heisLine, Darboux.rho, schr]) h
  exact ⟨fun h2 => (hA F _ f f₁ g).2.2.1 _ h2 h1, fun e => e ▸ h1⟩

end

theorem exists_chr (B : Base F E) (hB : B.IsGood σ) (m : ℕ) :
    ∃ χ : Chr F E, IsHecke F E χ ∧ ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m := by
  obtain ⟨χ, hχ, hr⟩ := GlobalTheory.T.exists_hecke_character_restriction F E σ B hB
  refine ⟨χ ^ m, ⟨hχ.1.pow m, fun x => ?_⟩, fun a => ?_⟩
  · rw [MonoidHom.pow_apply, hχ.2 x, one_pow]
  · rw [MonoidHom.pow_apply, Circle.coe_pow, hr a]
    split_ifs <;> simp

theorem exists_modelChange_pol : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d) (M M' : Model σ X W), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    M.IsGood B.ψ → M'.IsGood B.ψ →
    ∃ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M' 1 1 ∅ e ∧
      ∃ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
        (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ),
        Function.Surjective ei ∧ (M.Pol B.ψ B.emb).map (ei : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) = M'.Pol B.ψ B.emb ∧
        (∀ v, ev v (M.vac v) = M'.vac v ∧ (SB _).map (ev v) = SB _) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v) := by
  intro hK F E _ _ _ _ _ σ B n d r s r' s' X W M M' hB hX hW hM hM'
  classical
  obtain ⟨χX, hcX, rX⟩ := exists_chr B hB n
  obtain ⟨χW, hcW, rW⟩ := exists_chr B hB d
  obtain ⟨om, hom⟩ := GlobalTheory.WeilExGen.exists_isWeil hK F E σ B hB n d X W r s r' s' hX hW M hM χX χW hcX hcW rX rW
  obtain ⟨om', hom'⟩ := GlobalTheory.WeilExGen.exists_isWeil hK F E σ B hB n d X W r s r' s' hX hW M' hM' χX χW hcX hcW rX rW
  obtain ⟨e, -, -, hE, hbij, -⟩ := GlobalTheory.T.theta_model_change hK F E σ B n d X W M χX χW om r s r' s'
    ⟨hB, hX, hW, hM, hcX, hcW, rX, rW, hom⟩ M' om' ⟨hB, hX, hW, hM', hcX, hcW, rX, rW, hom'⟩
  obtain ⟨ei, ev, -, hv, hl⟩ := hE.loc
  have hg : finPr M.vac ∈ SB _ := finPr_mem _ (fun v => (hM.vac v).1) hM.std
  have hg' : finPr M'.vac ∈ SB _ := finPr_mem _ (fun v => (hM'.vac v).1) hM'.std
  obtain ⟨y, hy⟩ := exists_finPr_ne M.vac (fun v => (hM.vac v).2.1) hM.std
  obtain ⟨y', hy'⟩ := exists_finPr_ne M'.vac (fun v => (hM'.vac v).2.1) hM'.std
  have mem : ∀ (f : SInf F (Fin n × Fin d)) g, g ∈ SB (Fin n × Fin d → Af F) → pureA F f g ∈ schA F (Fin n × Fin d) :=
    fun f g h => Submodule.subset_span ⟨f, g, h, rfl⟩
  have hvac : ∀ f : SInf F (Fin n × Fin d), e (pureA F f (finPr M.vac)) = pureA F (ei f) (finPr M'.vac) := fun f => by
    have := hl f M.vac (fun v => (hM.vac v).1) (Eventually.of_forall fun _ => rfl)
    simp only [fun v => (hv v).1] at this
    exact this
  have hinj : Function.Injective ei := (injective_iff_map_eq_zero ei).2 fun f hf => by
    have h1 : e (pureA F f (finPr M.vac)) = e 0 := by
      rw [hvac, hf, map_zero]; funext x; simp [pureA]
    have h2 := hbij.injOn (mem f _ hg) (zero_mem _) h1
    refine SchwartzMap.ext fun x => ?_
    have h3 := congrFun h2 (pt x y)
    rw [pureA_pt] at h3
    exact (mul_eq_zero.1 h3).resolve_right hy
  have hsl : ∀ Φ ∈ schA F (Fin n × Fin d), ∃ f, ∀ x, e Φ (pt x y') = ei f x := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | zero => exact ⟨0, fun x => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨f, hf⟩ := ha
      obtain ⟨g, hg⟩ := hb
      exact ⟨f + g, fun x => by simp [hf, hg]⟩
    | smul c a _ ha =>
      obtain ⟨f, hf⟩ := ha
      exact ⟨c • f, fun x => by simp [hf]⟩
    | mem Φ hΦ =>
      obtain ⟨f, g, hg, rfl⟩ := hΦ
      replace hg := GlobalTheory.T.schwartzBruhat_finiteAdeles_mem_span_restrictedProducts F _ g hg
      induction hg using Submodule.span_induction with
      | zero => exact ⟨0, fun x => by
          rw [show pureA F f 0 = 0 from funext fun _ => mul_zero _]; simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨f₁, hf⟩ := ha
        obtain ⟨f₂, hg⟩ := hb
        exact ⟨f₁ + f₂, fun x => by
          rw [show pureA F f (a + b) = pureA F f a + pureA F f b from funext fun _ => mul_add _ _ _]; simp [hf, hg]⟩
      | smul c a _ ha =>
        obtain ⟨f₁, hf⟩ := ha
        exact ⟨c • f₁, fun x => by
          rw [show pureA F f (c • a) = c • pureA F f a from funext fun _ => mul_left_comm _ _ _]; simp [hf]⟩
      | mem p hp =>
        obtain ⟨φ, hφ, hs, rfl⟩ := hp
        have h1 := hl f φ hφ (by filter_upwards [hs, hM.std] with v h1 h2 using h1.trans h2.symm)
        refine ⟨finPr (fun v => ev v (φ v)) y' • f, fun x => ?_⟩
        rw [pure_eq, pure_eq] at h1
        refine (congrFun h1 _).trans ?_
        rw [pureA_pt]
        simp [mul_comm]
  have hsurj : Function.Surjective ei := fun g => by
    obtain ⟨Φ, hΦ, h1⟩ := hbij.surjOn (mem g _ hg')
    obtain ⟨f, hf⟩ := hsl Φ hΦ
    refine ⟨(finPr M'.vac y')⁻¹ • f, ?_⟩
    refine SchwartzMap.ext fun x => ?_
    have h2 := hf x
    rw [h1, pureA_pt] at h2
    rw [map_smul, smul_apply, ← h2, smul_eq_mul]
    field_simp
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ B.ψ _ _ M.co hB.std
  obtain ⟨D', hD'⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ B.ψ _ _ M'.co hB.std
  have Heisenberg₂ : ∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ u Φ) = M'.co.rho B.ψ u (e Φ) := by
    intro u Φ hΦ
    have h1 : ∀ m : ℕ, incM F (1 : Matrix (Fin m) (Fin m) E) = 1 := fun m => Matrix.map_one _ (map_zero _) (map_one _)
    have := hE.Heisenberg₂ u Φ hΦ
    rwa [h1, h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at this
  refine ⟨e, hE, ei, ev, hsurj, ?_, hv, hl⟩
  refine pol_map M M' B.ψ B.emb (fun u f => D u f) (fun u f => D' u f)
    (fun u hu f => actsD_iff GlobalTheory.T.archActionReadings_compatible M B.ψ u f _ (hD u hu f).1) (fun u hu f => actsD_iff GlobalTheory.T.archActionReadings_compatible M' B.ψ u f _ (hD' u hu f).1)
    _ ⟨hinj, hsurj⟩ fun u hu f => ?_
  refine SchwartzMap.ext fun x => ?_
  have h1 := (hD u hu f).1 _ hg _ (GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n d X W X W M M' 1 1 ∅ e hM hM' hE _ (proj_adm x y'))
  have h2 := (hD' u hu (ei f)).1 _ hg' _ (proj_adm x y')
  simp only [LinearMap.comp_apply, Heisenberg₂ _ _ (mem f _ hg), hvac] at h1
  have h3 := h1.unique h2
  rw [LinearMap.proj_apply, LinearMap.proj_apply, pureA_pt, pureA_pt] at h3
  exact mul_right_cancel₀ hy' h3

end GlobalTheory.ThK.ModelPol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenbundleFrameAffineAtlas
section
noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem valF_eq_ev {K : Type} [Field K] {X : Scheme.{0}} (w : Sp K ⟶ X) (V : X.Opens) (hV : ⊤ ≤ w ⁻¹ᵁ V)
    (f : Γ(X, V)) : valF w V f = ev w V hV f :=
  GlobalTheory.Points.valR_eq w V hV f

theorem map_valF_eq_ev {K : Type} [Field K] {X : Scheme.{0}} (w : Sp K ⟶ X) (V : X.Opens) (hV : ⊤ ≤ w ⁻¹ᵁ V)
    {m n : Type} (A : Matrix m n Γ(X, V)) : A.map (valF w V) = A.map (ev w V hV) := by
  ext i j
  exact valF_eq_ev w V hV _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)}

def trA {k : ECh Y p} {M₀ : GChart Y} (hk : k.M = M₀) {U : Y.X.Opens} (hV : k.V ≤ U) {N : ℕ}
    (A₀ : Matrix (Fin (N + 1)) (Fin M₀.n) Γ(Y.X, U)) : Matrix (Fin (N + 1)) (Fin k.M.n) Γ(Y.X, k.V) :=
  (A₀.map (resG Y.X hV)).submatrix id (finCongr (congrArg (fun M : GChart Y => M.n) hk))

def trC {k : ECh Y p} {M₀ : GChart Y} (hk : k.M = M₀) {U : Y.X.Opens} (hV : k.V ≤ U) {N : ℕ}
    (C₀ : Matrix (Fin M₀.n) (Fin (N + 1)) Γ(Y.X, U)) : Matrix (Fin k.M.n) (Fin (N + 1)) Γ(Y.X, k.V) :=
  (C₀.map (resG Y.X hV)).submatrix (finCongr (congrArg (fun M : GChart Y => M.n) hk)) id

theorem trC_mul_trA {k : ECh Y p} {M₀ : GChart Y} (hk : k.M = M₀) {U : Y.X.Opens} (hV : k.V ≤ U) {N : ℕ}
    (A₀ : Matrix (Fin (N + 1)) (Fin M₀.n) Γ(Y.X, U)) (C₀ : Matrix (Fin M₀.n) (Fin (N + 1)) Γ(Y.X, U))
    (h : C₀ * A₀ = 1) : trC hk hV C₀ * trA hk hV A₀ = 1 := by
  subst hk
  ext i j
  have := congrArg (fun A => resG Y.X hV (A i j)) h
  simp only [Matrix.mul_apply, map_sum, map_mul] at this
  simp only [trC, trA, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.map_apply, finCongr_apply, Fin.cast_eq_self, id]
  rw [this, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem tw_tr [IsReduced Y.X] {k k' : ECh Y p} {M₀ M₀' : GChart Y} (hk : k.M = M₀) (hk' : k'.M = M₀')
    {U U' : Y.X.Opens} (hV : k.V ≤ U) (hV' : k'.V ≤ U') (hUM : U ⊓ U' ≤ M₀'.U ⊓ M₀.U) {N : ℕ}
    (A₀ : Matrix (Fin (N + 1)) (Fin M₀.n) Γ(Y.X, U)) (A₀' : Matrix (Fin (N + 1)) (Fin M₀'.n) Γ(Y.X, U'))
    (g : Γ(Y.X, U ⊓ U')ˣ)
    (H : ∀ (K : Type) [Field K] (w : Sp K ⟶ Y.X), ⊤ ≤ w ⁻¹ᵁ U → ⊤ ≤ w ⁻¹ᵁ U' →
      A₀.map (valF w _) = valF w _ g.val • (A₀'.map (valF w _) * (chg M₀'.toMChart M₀.toMChart).map (valF w _)))
    (S : Type) [CommRing S] (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ k.V) (h' : ⊤ ≤ x ⁻¹ᵁ k'.V)
    (hM : ⊤ ≤ x ⁻¹ᵁ (k'.M.U ⊓ k.M.U)) :
    ∃ a : Sˣ, (trA hk hV A₀).map (ev x _ h) =
      (a : S) • ((trA hk' hV' A₀').map (ev x _ h') * (chg k'.M.toMChart k.M.toMChart).map (ev x _ hM)) := by
  subst hk hk'
  have key : ∀ r j, resG Y.X (inf_le_left : U ⊓ U' ≤ U) (A₀ r j) =
      g.val * ∑ t, resG Y.X inf_le_right (A₀' r t) * resG Y.X hUM (chg k'.M.toMChart k.M.toMChart t j) := by
    intro r j
    refine GlobalTheory.TwistEmb.eq_of_valR fun K _ w hw => ?_
    have hw1 := le_preimage_mono inf_le_left hw
    have hw2 := le_preimage_mono inf_le_right hw
    have hw3 := le_preimage_mono hUM hw
    have e := congrFun (congrFun (H K w hw1 hw2) r) j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, valF_eq_ev w U hw1,
      valF_eq_ev w U' hw2, valF_eq_ev w _ hw, valF_eq_ev w _ hw3] at e
    show valF w _ _ = valF w _ _
    rw [valF_eq_ev w _ hw, valF_eq_ev w _ hw, ev_res w _ hw hw1, e, map_mul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul, ev_res w _ hw hw2, ev_res w _ hw hw3]
  have hx : ⊤ ≤ x ⁻¹ᵁ (U ⊓ U') := GlobalTheory.TwistEmb.le_inf' x (le_preimage_mono hV h) (le_preimage_mono hV' h')
  refine ⟨Units.map (ev x _ hx).toMonoidHom g, ?_⟩
  ext r j
  simp only [trA, Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.submatrix_apply, finCongr_apply,
    Fin.cast_eq_self, id, smul_eq_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  rw [ev_res x hV h (le_preimage_mono hV h), ← ev_res x inf_le_left hx (le_preimage_mono hV h), key, map_mul,
    map_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, ev_res x inf_le_right hx (le_preimage_mono hV' h'), ev_res x hV' h' (le_preimage_mono hV' h'),
    ev_res x hUM hx hM]

theorem exists_atlas : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)),
    PushInvertible Y.t.G Y.t.PP.L → Nonempty (Atlas Y p) := by
  intro E _ _ _ H Dw l Xo c Y p hP
  classical
  have : IsProper Y.s := projProper _ _ _ Y.proj
  have : IsReduced Y.X := by
    have : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x => by
      have := (Y.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  obtain ⟨L, N, σ, A, C, haff, hle, hCA, htw⟩ := GlobalTheory.TwistEmb.exists_twist_embedding c.F Y.X Y.s (GChart Y)
    (fun j => j.U) (fun j => j.n) (fun j j' => chg j.toMChart j'.toMChart) Y.proj
    (fun x => exists_gChart hP x)
    (fun K _ w j hw => by
      have hh : ⊤ ≤ w ⁻¹ᵁ (j.U ⊓ j.U) := GlobalTheory.TwistEmb.le_inf' w hw hw
      show (chg j.toMChart j.toMChart).map (valF w (j.U ⊓ j.U)) = 1
      rw [map_valF_eq_ev w _ hh, chg_map _ _ w hw hw hh, Module.Basis.toMatrix_self])
    (fun K _ w j j' j'' h1 h2 h3 => by
      show (chg j.toMChart j'.toMChart).map (valF w (j.U ⊓ j'.U)) *
        (chg j'.toMChart j''.toMChart).map (valF w (j'.U ⊓ j''.U)) =
        (chg j.toMChart j''.toMChart).map (valF w (j.U ⊓ j''.U))
      rw [map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h1 h2), map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h2 h3),
        map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h1 h3), chg_map _ _ w h1 h2, chg_map _ _ w h2 h3,
        chg_map _ _ w h1 h3, Module.Basis.toMatrix_mul_toMatrix])
  have hcovL : ∀ x : Y.X, ∃ i, x ∈ L.U i := fun x => exists_chart L.isLB x
  have hk : ∀ x : Y.X, ∃ i, ∃ k : ECh Y p, k.M = σ i ∧ x ∈ k.V ∧ IsAffineOpen k.V ∧ k.V ≤ L.U i := fun x => by
    obtain ⟨i, hi⟩ := hcovL x
    obtain ⟨k, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_eigenChart_affineOpen_within E H Dw l Xo c Y p (σ i) x (hle i hi) (L.U i) hi
    exact ⟨i, k, h1, h2, h3, h4⟩
  choose ix kx hkM hxk haffk hlek using hk
  have hc : IsCompact (Set.univ : Set Y.X) := by
    have e : (Set.univ : Set Y.X) = ⋃ i, ((L.U i : Y.X.Opens) : Set Y.X) :=
      (Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 (hcovL x)).symm
    rw [e]
    exact isCompact_iUnion fun i => (haff i).isCompact
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun x => ((kx x).V : Set Y.X)) (fun x => (kx x).V.isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxk x⟩)
  have hUM : ∀ i i', L.U i ⊓ L.U i' ≤ (σ i').U ⊓ (σ i).U := fun i i' =>
    le_inf (inf_le_right.trans (hle i')) (inf_le_left.trans (hle i))
  exact ⟨{
    B := t
    fin := inferInstance
    k := fun b => kx b.1
    aff := fun b => haffk b.1
    cov := fun x => by
      obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
      exact ⟨⟨z, hz⟩, hxz⟩
    N := N
    A := fun b => trA (hkM b.1) (hlek b.1) (A (ix b.1))
    C := fun b => trC (hkM b.1) (hlek b.1) (C (ix b.1))
    CA := fun b => trC_mul_trA _ _ _ _ (hCA _)
    tw := fun S _ x b b' h h' hM => tw_tr (hkM b.1) (hkM b'.1) (hlek b.1) (hlek b'.1) (hUM _ _) (A (ix b.1))
      (A (ix b'.1)) (L.g (ix b.1) (ix b'.1)) (fun K _ w hw hw' => htw K w _ _ hw hw') S x h h' hM }⟩

end GlobalTheory.FlagMod.FieldFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatFactorThroughLocalScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem flat_stalkClosedPointTo {S : Scheme.{0}} {R : CommRingCat.{0}} [IsLocalRing R]
    (ξ : Spec R ⟶ S) [Flat ξ] : (Scheme.stalkClosedPointTo ξ).hom.Flat := by
  unfold Scheme.stalkClosedPointTo
  rw [CommRingCat.hom_comp]
  exact (Flat.stalkMap ξ _).comp
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso R).hom))

theorem exists_faithfullyFlat_factor_localScheme :
    ∀ (S : Scheme.{0}) (R₁ : Type) [CommRing R₁] [IsLocalRing R₁] (ξ : Sp R₁ ⟶ S) (x : S),
      ξ (closedPoint R₁) = x → Flat ξ → ∃ ξ' : Sp R₁ ⟶ Spec (S.presheaf.stalk x),
        ξ' ≫ S.fromSpecStalk x = ξ ∧ Flat ξ' ∧ Surjective ξ' ∧ QuasiCompact ξ' := by
  intro S R₁ _ _ ξ x hx hf
  subst hx
  have hflat := flat_stalkClosedPointTo (R := CommRingCat.of R₁) ξ
  refine ⟨Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of R₁) ξ),
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of R₁) ξ,
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 hflat, ⟨?_⟩, inferInstance⟩
  set φ := (Scheme.stalkClosedPointTo (R := CommRingCat.of R₁) ξ).hom with hφ
  have hl : IsLocalHom φ := by rw [hφ]; infer_instance
  letI := φ.toAlgebra
  have : Module.Flat (S.presheaf.stalk (ξ (closedPoint R₁))) R₁ := hflat
  have : IsLocalHom (algebraMap (S.presheaf.stalk (ξ (closedPoint R₁))) R₁) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := S.presheaf.stalk (ξ (closedPoint R₁))) (B := R₁)
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := S.presheaf.stalk (ξ (closedPoint R₁))) (B := R₁)

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFanOrderIdealGluedClopenPieces
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.Poinc

theorem stalkId_finsetProd {X : Scheme.{0}} {ι : Type} (s : Finset ι) (K : ι → X.IdealSheafData) (x : X) :
    FinalTheorems.stalkId (∏ c ∈ s, K c) x = ∏ c ∈ s, FinalTheorems.stalkId (K c) x := by
  classical
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)
  simp only [ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ x ⟨U, hU⟩ hx]
  induction s using Finset.induction_on with
  | empty => simp [Ideal.map_top]
  | insert c s hc ih =>
    rw [Finset.prod_insert hc, Finset.prod_insert hc, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul, ih]

theorem stalkId_prodPow {X : Scheme.{0}} {ι : Type} [Fintype ι] (K : ι → X.IdealSheafData) (e : ι → ℕ) (x : X) :
    FinalTheorems.stalkId (∏ c, K c ^ e c) x = ∏ c, FinalTheorems.stalkId (K c) x ^ e c := by
  rw [stalkId_finsetProd]
  simp only [GlobalTheory.Vanishing.stalkId_pow]

theorem exists_valOn_of_pieces : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (j : F.X ⟶ S) (φ : InvFun ℤ) {ι : Type} [Fintype ι] (W : ι → Set S) (J : ι → S.IdealSheafData) (d : ι → ℕ), (∀ c, IsClopen (W c)) → (∀ x, ∃! c, x ∈ W c) → (∀ c, 1 ≤ d c) → (∀ c, ∀ x ∈ (J c).support, x ∈ W c ∧ x ∉ Set.range j) → (∀ c (T : Trait F) (ξ : Sp T.V ⟶ S), jK T.V ≫ ξ = T.y ≫ j → ξ (closedPoint T.V) ∈ W c → ∃ a : ℕ, (a : ℝ) = d c * φ.evalZ T.β ∧ idlAlong (J c) ξ = Ideal.span {T.ϖ ^ a}) → ∃ (d' : ℕ) (J' : S.IdealSheafData), 1 ≤ d' ∧ (∀ x ∈ J'.support, x ∉ Set.range j) ∧ ValOn F j φ J' d' := by
  intro o _ ζ g n F S j φ ι _ W J d _ huniq hd hsupp htr
  classical
  have hdvd : ∀ c, d c ∣ ∏ c, d c := fun c => Finset.dvd_prod_of_mem (s := Finset.univ) d (Finset.mem_univ c)
  have htop : ∀ c x, x ∉ W c → FinalTheorems.stalkId (J c) x = ⊤ := fun c x hx =>
    GlobalTheory.Vanishing.stalkId_eq_top (J c) fun hs => hx (hsupp c x hs).1
  refine ⟨∏ c, d c, ∏ c, J c ^ ((∏ c, d c) / d c), ?_, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun c _ => by have := hd c; omega)
  · intro x hx
    obtain ⟨c, hc, -⟩ := huniq x
    by_cases hs : x ∈ (J c).support
    · exact (hsupp c x hs).2
    · exfalso
      refine (mem_support_iff_stalkId _ x).1 hx ?_
      rw [stalkId_prodPow, ← Ideal.one_eq_top]
      refine Finset.prod_eq_one fun c' _ => ?_
      by_cases e : c' = c
      · subst e; rw [GlobalTheory.Vanishing.stalkId_eq_top (J c') hs, ← Ideal.one_eq_top, one_pow]
      · rw [htop c' x fun h => e ((huniq x).unique h hc), ← Ideal.one_eq_top, one_pow]
  · intro T ξ hξ
    obtain ⟨c, hc, -⟩ := huniq (ξ (closedPoint T.V))
    obtain ⟨a, ha, hJ⟩ := htr c T ξ hξ hc
    refine ⟨(∏ c, d c) / d c * a, ?_, ?_⟩
    · have hd0 : (d c : ℝ) ≠ 0 := by have := hd c; positivity
      rw [Nat.cast_mul, Nat.cast_div (hdvd c) hd0, ha]
      field_simp
    · unfold idlAlong at hJ ⊢
      rw [stalkId_prodPow, Finset.prod_eq_single c, Ideal.map_pow, hJ, Ideal.span_singleton_pow, ← pow_mul, mul_comm]
      · intro c' _ e
        rw [htop c' _ fun h => e ((huniq _).unique h hc), ← Ideal.one_eq_top, one_pow]
      · intro h; exact absurd (Finset.mem_univ c) h

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAffineCoverInfClosed
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_finite_affine_cover_infClosed : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R),
    IsSeparated s → QuasiCompact s → ∃ (J : Type) (_ : Finite J) (_ : SemilatticeInf J)
      (U : J → X.affineOpens), Monotone U ∧ (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) ∧
        ⨆ i, (U i).1 = ⊤ := by
  intro R _ X s hsep hqc
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have hdiag : IsAffineHom (pullback.diagonal s) := inferInstance
  have hinf : ∀ U V : X.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V) :=
    fun U V hU hV => isAffineHom_diagonal_iff.mp hdiag ⊤ (isAffineOpen_top _) U (by simp) V
      (by simp) hU hV
  obtain ⟨S, hS, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).mp
    (by simpa using isCompact_univ)
  set A : Set X.Opens := infClosure ((fun i : X.affineOpens => i.1) '' S) with hAdef
  have hA : ∀ U ∈ A, IsAffineOpen U :=
    infClosure_min (t := {U | IsAffineOpen U}) (by rintro _ ⟨i, -, rfl⟩; exact i.2)
      (fun a ha b hb => hinf a b ha hb)
  letI inst : SemilatticeInf A :=
    Subtype.semilatticeInf (fun _ _ ha hb => infClosed_infClosure ha hb)
  haveI hfin : Finite A := ((hS.image _).infClosure).to_subtype
  refine ⟨A, hfin, inst, fun j => ⟨j.1, hA j.1 j.2⟩, fun a b h => h, fun i j => rfl, ?_⟩
  apply top_le_iff.mp
  rw [e]
  exact iSup₂_le fun i hi => le_iSup_of_le (⟨i.1, subset_infClosure ⟨i, hi, rfl⟩⟩ : A) le_rfl

end GlobalTheory
end

