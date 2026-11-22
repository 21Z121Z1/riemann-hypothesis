import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1736
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1749
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0354

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForLeviMatrix
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LeviOp

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem map_inv_mul {S : Type} [CommRing S] (g : F →+* S) (A : Matrix κ κ F) (h : IsUnit A.det) :
    A⁻¹.map g * A.map g = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul A h, Matrix.map_one g (map_zero g) (map_one g)]

theorem map_mul_inv {S : Type} [CommRing S] (g : F →+* S) (A : Matrix κ κ F) (h : IsUnit A.det) :
    A.map g * A⁻¹.map g = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv A h, Matrix.map_one g (map_zero g) (map_one g)]

theorem hom_mulVec {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) (g : F →+* S) (g' : F →+* T)
    (hg : f.comp g = g') (M : Matrix κ κ F) (x : κ → S) (i : κ) :
    f ((M.map g *ᵥ x) i) = (M.map g' *ᵥ (fun j => f (x j))) i := by
  subst hg
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem spAct_levi {R : Type} [CommRing R] [Algebra F R] (A : Matrix κ κ F) (w : (κ → R) × (κ → R)) :
    GlobalTheory.SympChange.spAct (GlobalTheory.SympChange.leviM A) w =
      (A.map (algebraMap F R) *ᵥ w.1, (A⁻¹.map (algebraMap F R))ᵀ *ᵥ w.2) := by
  unfold GlobalTheory.SympChange.spAct GlobalTheory.SympChange.leviM
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec]
  ext k <;> simp [Matrix.transpose_map]

theorem schr_levi {R : Type} [CommRing R] [Algebra F R] [Invertible (2 : R)] (ψ : AddChar R ℂ)
    (A : Matrix κ κ F) (hA : IsUnit A.det) (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    (fun x => schr ψ w φ (A⁻¹.map (algebraMap F R) *ᵥ x)) =
      schr ψ (GlobalTheory.SympChange.spAct (GlobalTheory.SympChange.leviM A) w) (fun x => φ (A⁻¹.map (algebraMap F R) *ᵥ x)) := by
  rw [spAct_levi]
  funext x
  simp only [GlobalTheory.WeilM.schr]
  have h1 := map_inv_mul (algebraMap F R) A hA
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec,
    Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

def homeo {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (g : F →+* S) (A : Matrix κ κ F)
    (hA : IsUnit A.det) : (κ → S) ≃ₜ (κ → S) where
  toFun x := A⁻¹.map g *ᵥ x
  invFun x := A.map g *ᵥ x
  left_inv x := by simp only [Matrix.mulVec_mulVec, map_mul_inv g A hA, Matrix.one_mulVec]
  right_inv x := by simp only [Matrix.mulVec_mulVec, map_inv_mul g A hA, Matrix.one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem homeo_apply {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (g : F →+* S)
    (A : Matrix κ κ F) (hA : IsUnit A.det) (x : κ → S) : homeo g A hA x = A⁻¹.map g *ᵥ x := rfl

def linEquiv {S : Type} [CommRing S] [Algebra ℝ S] [TopologicalSpace S] [IsTopologicalRing S] (g : F →+* S)
    (A : Matrix κ κ F) (hA : IsUnit A.det) : (κ → S) ≃L[ℝ] (κ → S) where
  toFun x := A⁻¹.map g *ᵥ x
  invFun x := A.map g *ᵥ x
  map_add' x y := Matrix.mulVec_add _ x y
  map_smul' c x := Matrix.mulVec_smul _ c x
  left_inv x := by simp only [Matrix.mulVec_mulVec, map_mul_inv g A hA, Matrix.one_mulVec]
  right_inv x := by simp only [Matrix.mulVec_mulVec, map_inv_mul g A hA, Matrix.one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem sb_comp {X : Type} [TopologicalSpace X] (h : X ≃ₜ X) {φ : X → ℂ} (hφ : φ ∈ SB X) : φ ∘ h ∈ SB X :=
  ⟨hφ.1.comp_continuous h.continuous, hφ.2.comp_homeomorph h⟩

variable [NumberField F]

def evIr : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem mulVec_mem {v : Pl F} (M : Matrix κ κ F)
    (hM : ∀ i j, algebraMap F (Fv F v) (M i j) ∈ v.adicCompletionIntegers F) (x : κ → Fv F v)
    (hx : ∀ i, x i ∈ v.adicCompletionIntegers F) (i : κ) :
    (M.map (algebraMap F (Fv F v)) *ᵥ x) i ∈ v.adicCompletionIntegers F := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact sum_mem fun j _ => mul_mem (hM i j) (hx j)

theorem eventually_int (M : Matrix κ κ F) :
    ∀ᶠ v : Pl F in cofinite, ∀ i j, algebraMap F (Fv F v) (M i j) ∈ v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  exact fun i j => (algebraMap F (Af F) (M i j)).2

open scoped Classical in

theorem hasOp_levi : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl F, ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix κ κ F), IsUnit A.det →
    GlobalTheory.SympChange.HasOp ψ (GlobalTheory.SympChange.leviM A) := by
  intro F _ _ ψ _ _ _ κ _ _ A hA
  let gI : F →+* mixedEmbedding.mixedSpace F := (evIr (F := F)).comp (algebraMap F (AF F))
  let gF : F →+* FiniteAdeleRing (𝓞 F) F := (RingHom.snd _ _).comp (algebraMap F (AF F))
  let L := linEquiv (κ := κ) gI A hA
  refine ⟨LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x),
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L,
    fun v => LinearMap.funLeft ℂ ℂ (fun x : κ → Fv F v => A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm f, ?_⟩
    refine SchwartzMap.ext fun x => ?_
    simp
  · have key : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
        LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x) (pureA F f g) =
          pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f) (g ∘ homeo gF A hA) := by
      intro f g
      funext x
      simp only [LinearMap.funLeft_apply, pureA, Function.comp_apply, homeo_apply,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
      congr 1
      · congr 1
        funext i
        exact hom_mulVec evIr (algebraMap F (AF F)) gI rfl A⁻¹ x i
      · congr 1
        funext i
        exact hom_mulVec (RingHom.snd _ _) (algebraMap F (AF F)) gF rfl A⁻¹ x i
    have hle : schA F κ ≤ (schA F κ).comap
        (LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, g, hg, rfl⟩
      show _ ∈ schA F κ
      rw [key]
      exact Submodule.subset_span ⟨_, _, sb_comp (homeo gF A hA) hg, rfl⟩
    exact fun Φ hΦ => hle hΦ
  · intro w Φ _
    exact schr_levi ψ A hA w Φ
  · intro v
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun φ hφ => sb_comp (homeo _ A hA) hφ) ?_
    intro φ hφ
    refine ⟨φ ∘ (homeo (algebraMap F (Fv F v)) A hA).symm, sb_comp _ hφ, ?_⟩
    funext x
    simp only [LinearMap.funLeft_apply, Function.comp_apply]
    exact congrArg φ ((homeo (algebraMap F (Fv F v)) A hA).symm_apply_apply x)
  · intro v φ _ h
    funext x
    have := congrFun h ((homeo (algebraMap F (Fv F v)) A hA).symm x)
    simp only [LinearMap.funLeft_apply, Pi.zero_apply] at this
    have hx : A⁻¹.map (algebraMap F (Fv F v)) *ᵥ (homeo (algebraMap F (Fv F v)) A hA).symm x = x :=
      (homeo (algebraMap F (Fv F v)) A hA).apply_symm_apply x
    rw [hx] at this
    exact this
  · intro v w φ _
    exact schr_levi (GlobalTheory.LatVac.psiAt ψ v) A hA w φ
  · filter_upwards [eventually_int A, eventually_int A⁻¹] with v hA1 hA2
    funext x
    have hiff : (∀ i, (A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x) i ∈ v.adicCompletionIntegers F) ↔
        ∀ i, x i ∈ v.adicCompletionIntegers F := by
      constructor
      · intro h i
        have e : x = A.map (algebraMap F (Fv F v)) *ᵥ (A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x) :=
          ((homeo (algebraMap F (Fv F v)) A hA).symm_apply_apply x).symm
        rw [e]
        exact mulVec_mem A hA1 _ h i
      · intro h i
        exact mulVec_mem A⁻¹ hA2 x h i
    show Set.indicator _ _ _ = Set.indicator _ _ _
    by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
    · rw [Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hiff.2 hx),
        Set.indicator_of_mem (show x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx)]
      rfl
    · rw [Set.indicator_of_notMem (show _ ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from mt hiff.1 hx),
        Set.indicator_of_notMem (show x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx)]
  · intro f φ _ _
    funext x
    simp only [LinearMap.funLeft_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply]
    congr 1
    · congr 1
      funext i
      exact hom_mulVec evIr (algebraMap F (AF F)) gI rfl A⁻¹ x i
    · refine finprod_congr fun v => congrArg (φ v) ?_
      funext i
      exact hom_mulVec (evFin F v).toRingHom (algebraMap F (AF F)) (algebraMap F (Fv F v))
        (RingHom.ext fun c => (evFin F v).commutes c) A⁻¹ x i

end GlobalTheory.LeviOp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilSkewIdealLatticeUnitVectorUnimodularEigen
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall.CvEig

variable {D : D7}

theorem norm_eq_one_of_modulusOneAll {c : ℂ} (h : Mod1All c) : ‖c‖ = 1 := by
  obtain ⟨hx, h2⟩ := h
  simpa using h2 Qbar.val

theorem int_of_inc {b : D.host.E} (hb : inc D b ∈ OhE D) : ∃ o : 𝓞 D.host.E, (o : D.host.E) = b := by
  have h := (VacMove.moves_one D 1 (fun _ => b)).2 (fun i => by simpa using hb)
  simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at h
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 (h 0)
  exact ⟨o, ho⟩

theorem exists_nat_clear {N : ℕ} (P : Matrix (Fin N) (Fin N) (AE D)) :
    ∃ n : ℕ, 0 < n ∧ ∀ s : Fin N → AE D, (∀ j, s j ∈ OhE D) →
      ∀ i, P.mulVec (fun j => (n : AE D) * s j) i ∈ OhE D := by
  obtain ⟨n, hn, hP⟩ := VacMove.exists_mat_denom P
  refine ⟨n, hn, fun s hs i => ?_⟩
  simp only [Matrix.mulVec, dotProduct]
  refine sum_mem fun j _ => ?_
  have : P i j * ((n : AE D) * s j) = ((n : AE D) * P i j) * s j := by ring
  rw [this]
  exact mul_mem (hP i j) (hs j)

end GlobalTheory.BotPairSmall.CvEig

namespace GlobalTheory.BotPairSmall.CvEig

variable {D : D7}

theorem lam_int_mul {N : ℕ} (𝔫 : Ideal (𝓞 D.host.E)) {h : GL (Fin N) (AE D)}
    (hL : Moves D h (skewLat D 𝔫 N)) {k : Matrix (Fin N) (Fin N) (AE D)} (hk : ∀ i j, k i j ∈ OhE D)
    (u : Fin N → AE D)
    (hu : ∀ i, (((h⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))).mulVec u i ∈ OhE D) :
    ∀ i, (((h⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))).mulVec (k.mulVec u) i ∈ OhE D := by
  obtain ⟨n, hn, hcl⟩ := exists_nat_clear (((h⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)))
  obtain ⟨M, hM, hMs⟩ := GlobalTheory.FunObj.CosetTT.skewLat_smul (D := D) 𝔫 N
  choose y s hs e using fun j => GlobalTheory.TrueTheta.approx D (u j) hn
  have hy : y ∈ skewLat D 𝔫 N := by
    rw [hL y]
    intro i
    have : (fun j => inc D (y j)) = u + fun j => (n : AE D) * s j := funext fun j => e j
    rw [this, Matrix.mulVec_add]
    exact add_mem (hu i) (hcl s hs i)
  choose b t ht eb using fun q : Fin N × Fin N => GlobalTheory.TrueTheta.approx D (k q.1 q.2) (Nat.mul_pos hn hM)
  have hb : ∀ q, ∃ o : 𝓞 D.host.E, (o : D.host.E) = b q := fun q =>
    int_of_inc (by rw [eb q]; exact add_mem (hk _ _) (mul_mem (natCast_mem _ _) (ht q)))
  choose o ho using hb
  have hzL : (fun i => ∑ j, b (i, j) * y j) ∈ skewLat D 𝔫 N := by
    have hy' := hy
    simp only [skewLat, Submodule.mem_pi, Set.mem_univ, true_implies] at hy' ⊢
    intro i
    refine sum_mem fun j _ => ?_
    rw [← ho (i, j)]
    have : ((o (i, j) : 𝓞 D.host.E) : D.host.E) * y j = o (i, j) • y j := (Algebra.smul_def _ _).symm
    rw [this]
    exact Submodule.smul_mem _ _ (hy' j)
  have hMy : ∀ j, inc D ((M : D.host.E) * y j) ∈ OhE D := by
    intro j
    have h1 := hMs y hy
    simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at h1
    obtain ⟨o', ho'⟩ := Submodule.mem_one.1 (h1 j)
    have : ((M : 𝓞 D.host.E) • y) j = (M : D.host.E) * y j := by simp [Algebra.smul_def]
    rw [← this, ← ho']
    exact VacMove.inc_int D o'
  have hw : ∀ i, (∑ j, t (i, j) * inc D ((M : D.host.E) * y j)) ∈ OhE D := fun i =>
    sum_mem fun j _ => mul_mem (ht _) (hMy j)
  have hks : ∀ i, k.mulVec s i ∈ OhE D := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun j _ => mul_mem (hk _ _) (hs j)
  have key : k.mulVec u = (fun i => inc D (∑ j, b (i, j) * y j)) -
      (fun i => (n : AE D) * ∑ j, t (i, j) * inc D ((M : D.host.E) * y j)) -
      (fun i => (n : AE D) * k.mulVec s i) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, map_sum, map_mul, map_natCast, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 := e j
    have e2 := eb (i, j)
    push_cast at e2
    linear_combination (-inc D (y j)) * e2 - k i j * e1
  rw [key]
  intro i
  rw [Matrix.mulVec_sub, Matrix.mulVec_sub]
  exact sub_mem (sub_mem ((hL _).1 hzL i) (hcl _ hw i)) (hcl _ hks i)

theorem moves_int_mul {N : ℕ} (𝔫 : Ideal (𝓞 D.host.E)) {h k : GA D N}
    (hL : Moves D (h : GL (Fin N) (AE D)) (skewLat D 𝔫 N)) (hk : k ∈ intG D N) :
    Moves D ((k * h : GA D N) : GL (Fin N) (AE D)) (skewLat D 𝔫 N) := by
  have hk' := (mem_intG k).1 hk
  intro x
  rw [hL x, Subgroup.coe_mul, _root_.mul_inv_rev, Units.val_mul]
  constructor
  · intro hx i
    rw [← Matrix.mulVec_mulVec]
    exact lam_int_mul 𝔫 hL (fun i j => (hk' i j).2) _ hx i
  · intro hx i
    rw [← Matrix.mulVec_mulVec] at hx
    have := lam_int_mul 𝔫 hL (k := ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)))
      (fun i j => (hk' i j).1) _ hx i
    have hkk : ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)).mulVec
        ((((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)).mulVec
          (fun j => inc D (x j))) = fun j => inc D (x j) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rwa [hkk] at this

end GlobalTheory.BotPairSmall.CvEig

namespace GlobalTheory.BotPairSmall.CvEig

theorem om_unitVec_eig : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ g ∈ intG D a, ∀ g' ∈ intG D d, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om g g' (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) = c • (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho g hg g' hg'
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have he := hv.1
  have hT := VacMove.vac_TT h1 hc he
  have hI : Inp D := GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied D
  have hev : Even (a * d) := hd.mul_left a
  have hcc : D.host.conj • D.host.conj • 𝔪 = 𝔪 := by
    have h2 : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun x => VacMove.conj_conj D x
    rw [smul_smul, h2, one_smul]
  have hcop' : IsCoprime (D.host.conj • 𝔪) (D.host.conj • D.host.conj • 𝔪) := by
    rw [hcc, Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hcop
  obtain ⟨h, -, -, hmv, -, -⟩ := GlobalTheory.T.exists_splitSupported_unitary_moving_to_selfDualSkewLattice D (D.host.conj • 𝔪) (GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm) hcop' d
  obtain ⟨c1, hc1, he1, -⟩ := GlobalTheory.NormSum.vacuum_under_adelic_pair D hI ⊤ δ hc a d hev e0 he W 1 h (stdL D a)
    (skewLat D (D.host.conj • 𝔪) d) (VacMove.moves_one D a) hmv
  have hg1 : Moves D (g : GL (Fin a) (AE D)) (stdL D a) := by
    simpa using VacMove.moves_mul_int hg (VacMove.moves_one D a)
  have hmv2 := moves_int_mul (D.host.conj • 𝔪) hmv hg'
  obtain ⟨c2, hc2, he2, -⟩ := GlobalTheory.NormSum.vacuum_under_adelic_pair D hI ⊤ δ hc a d hev e0 he W g (g' * h) (stdL D a)
    (skewLat D (D.host.conj • 𝔪) d) hg1 hmv2
  have n1 := norm_eq_one_of_modulusOneAll hc1
  have n2 := norm_eq_one_of_modulusOneAll hc2
  have c1ne : c1 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at n1; exact zero_ne_one n1
  set F := Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0
    with hF
  have hF1 : F = c1⁻¹ • W.Om 1 h e0 := by
    rw [he1]; funext z; simp only [Pi.smul_apply, smul_eq_mul]; rw [← mul_assoc, inv_mul_cancel₀ c1ne, one_mul]
  refine ⟨c1⁻¹ * c2, by rw [norm_mul, norm_inv, n1, n2]; norm_num, ?_⟩
  have hm2 := W.mul g 1 g' h e0 hT
  rw [mul_one] at hm2
  conv_lhs => rw [hF1, W.smul _ _ _ _ (W.maps 1 h e0 hT), ← hm2, he2]
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.BotPairSmall.CvEig
end
end

