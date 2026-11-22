import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetNeZeroOfLowestFormNeZeroPresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplementOfCharactersUniqueUpToConj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

namespace GlobalTheory.CharCancel

section Cancel

variable {K Γ V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem ennreal_volume_ratio_step_cancel (a : Γ → V →ₗ[K] V) (b : Γ → W →ₗ[K] W) (c : Γ → K) (e : (V × K) ≃ₗ[K] (W × K))
    (h : ∀ g v x, e (a g v, c g * x) = (b g (e (v, x)).1, c g * (e (v, x)).2))
    (v₀ : V) (hv : ∀ g, a g v₀ = c g • v₀) (hd : (e (v₀, 1)).2 ≠ 0) :
    ∃ f : V ≃ₗ[K] W, ∀ g v, f (a g v) = b g (f v) := by
  rcases hE : e (v₀, 1) with ⟨w', δ⟩
  have hd0 : δ ≠ 0 := by rw [hE] at hd; exact hd
  have hb : ∀ g, b g w' = c g • w' := by
    intro g
    have h1 := h g v₀ 1
    have h2 : ((a g v₀, c g * 1) : V × K) = c g • ((v₀, 1) : V × K) := by
      rw [hv]; simp
    rw [h2, map_smul, hE] at h1
    have h3 := congrArg Prod.fst h1
    simp at h3
    exact h3.symm
  refine ⟨{ toFun := fun v => (e (v, 0)).1 - ((e (v, 0)).2 / δ) • w'
            invFun := fun w => (e.symm (w, 0)).1 - (e.symm (w, 0)).2 • v₀
            map_add' := ?_, map_smul' := ?_, left_inv := ?_, right_inv := ?_ }, ?_⟩
  · intro x y
    have hxy : ((x + y, (0 : K)) : V × K) = (x, 0) + (y, 0) := by simp
    rw [hxy, map_add]
    simp only [Prod.fst_add, Prod.snd_add, add_div, add_smul]
    abel
  · intro s x
    have hsx : ((s • x, (0 : K)) : V × K) = s • (x, 0) := by simp
    rw [hsx, map_smul]
    simp [smul_sub, smul_smul, mul_div_assoc]
  · intro v
    dsimp only
    have key : (((e (v, 0)).1 - ((e (v, 0)).2 / δ) • w', (0 : K)) : W × K) =
        e (v, 0) - ((e (v, 0)).2 / δ) • e (v₀, 1) := by
      rw [hE]
      ext
      · simp
      · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
        rw [div_mul_cancel₀ _ hd0, sub_self]
    rw [key, map_sub, map_smul, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    simp
  · intro w
    dsimp only
    have key : (((e.symm (w, 0)).1 - (e.symm (w, 0)).2 • v₀, (0 : K)) : V × K) =
        e.symm (w, 0) - (e.symm (w, 0)).2 • (v₀, 1) := by
      ext <;> simp
    rw [key, map_sub, map_smul, LinearEquiv.apply_symm_apply, hE]
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, zero_sub]
    rw [neg_div, mul_div_cancel_right₀ _ hd0, neg_smul, sub_neg_eq_add, sub_add_cancel]
  · intro g v
    show (e (a g v, 0)).1 - ((e (a g v, 0)).2 / δ) • w' = b g ((e (v, 0)).1 - ((e (v, 0)).2 / δ) • w')
    have h1 := h g v 0
    rw [mul_zero] at h1
    rw [h1, map_sub, map_smul, hb, smul_smul]
    dsimp only
    rw [show c g * (e (v, 0)).2 / δ = (e (v, 0)).2 / δ * c g by ring]

theorem cancel_one (a : Γ → V →ₗ[K] V) (b : Γ → W →ₗ[K] W) (c : Γ → K) (e : (V × K) ≃ₗ[K] (W × K))
    (h : ∀ g v x, e (a g v, c g * x) = (b g (e (v, x)).1, c g * (e (v, x)).2)) :
    ∃ f : V ≃ₗ[K] W, ∀ g v, f (a g v) = b g (f v) := by
  by_cases hd : (e ((0 : V), (1 : K))).2 = 0
  · rcases hq : e.symm ((0 : W), (1 : K)) with ⟨v₁, d'⟩
    have hq' : e (v₁, d') = ((0 : W), (1 : K)) := by rw [← hq]; simp
    have hv1 : ∀ g, a g v₁ = c g • v₁ := by
      intro g
      have h1 := h g v₁ d'
      rw [hq'] at h1
      simp only [map_zero, mul_one] at h1
      have h2 : e (c g • v₁, c g * d') = ((0 : W), c g) := by
        have h3 : ((c g • v₁, c g * d') : V × K) = c g • (v₁, d') := by simp
        rw [h3, map_smul, hq']; simp
      have h4 := e.injective (h1.trans h2.symm)
      simpa using congrArg Prod.fst h4
    have hd1 : (e (v₁, 1)).2 ≠ 0 := by
      have h5 : ((v₁, 1) : V × K) = (v₁, d') + (1 - d') • ((0 : V), (1 : K)) := by ext <;> simp
      rw [h5, map_add, map_smul, hq']
      simp [hd]
    exact ennreal_volume_ratio_step_cancel a b c e h v₁ hv1 hd1
  · exact ennreal_volume_ratio_step_cancel a b c e h 0 (fun g => by simp) hd

def splitFirst (V : Type) [AddCommGroup V] [Module K V] (t : ℕ) :
    ((V × (Fin t → K)) × K) ≃ₗ[K] (V × (Fin (t + 1) → K)) where
  toFun p := (p.1.1, Fin.cons p.2 p.1.2)
  invFun q := ((q.1, fun j => q.2 j.succ), q.2 0)
  map_add' p q := by
    refine Prod.ext rfl (funext fun j => ?_)
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  map_smul' x p := by
    refine Prod.ext rfl (funext fun j => ?_)
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  left_inv p := by simp
  right_inv q := by
    refine Prod.ext rfl (funext fun j => ?_)
    refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem cancel_fin (a : Γ → V →ₗ[K] V) (b : Γ → W →ₗ[K] W) (t : ℕ) :
    ∀ (c : Fin t → Γ → K) (e : (V × (Fin t → K)) ≃ₗ[K] (W × (Fin t → K))),
    (∀ g v x, e (a g v, fun j => c j g * x j) = (b g (e (v, x)).1, fun j => c j g * (e (v, x)).2 j)) →
    ∃ f : V ≃ₗ[K] W, ∀ g v, f (a g v) = b g (f v) := by
  induction t with
  | zero =>
    intro c e h
    refine ⟨((LinearEquiv.prodUnique : (V × (Fin 0 → K)) ≃ₗ[K] V).symm.trans e).trans
      (LinearEquiv.prodUnique : (W × (Fin 0 → K)) ≃ₗ[K] W), fun g v => ?_⟩
    have hx : ((a g v, fun j => c j g * (default : Fin 0 → K) j) : V × (Fin 0 → K)) = (a g v, default) :=
      Prod.ext rfl (Subsingleton.elim _ _)
    have h1 := h g v default
    rw [hx] at h1
    show (e (a g v, default)).1 = b g (e (v, default)).1
    rw [h1]
  | succ t ih =>
    intro c e h
    let S := splitFirst (K := K) V t
    let T := splitFirst (K := K) W t
    let a' : Γ → (V × (Fin t → K)) →ₗ[K] (V × (Fin t → K)) := fun g =>
      (a g).prodMap (LinearMap.pi fun j => c j.succ g • LinearMap.proj j)
    let b' : Γ → (W × (Fin t → K)) →ₗ[K] (W × (Fin t → K)) := fun g =>
      (b g).prodMap (LinearMap.pi fun j => c j.succ g • LinearMap.proj j)
    refine (cancel_one a' b' (c 0) ((S.trans e).trans T.symm) ?_).elim fun f' hf' => ?_
    · intro g p y
      obtain ⟨v, x⟩ := p
      have hS : ∀ (u : V) (z : Fin t → K) (s : K), S ((u, z), s) = (u, Fin.cons s z) := fun _ _ _ => rfl
      have hT : ∀ q : W × (Fin (t + 1) → K), T.symm q = ((q.1, fun j => q.2 j.succ), q.2 0) := fun _ => rfl
      have ha : a' g (v, x) = (a g v, fun j => c j.succ g * x j) := rfl
      have hcons : (Fin.cons (c 0 g * y) (fun j => c j.succ g * x j) : Fin (t + 1) → K) =
          fun j => c j g * (Fin.cons y x : Fin (t + 1) → K) j := by
        funext j; refine Fin.cases ?_ (fun j => ?_) j <;> simp
      simp only [LinearEquiv.trans_apply]
      rw [ha, hS, hS, hcons, h g v (Fin.cons y x : Fin (t + 1) → K), hT, hT]
      rfl
    · exact ih (fun j => c j.succ) f' (fun g v x => hf' g (v, x))

end Cancel

theorem overK_apply {Γ A : Type} [Group Γ] [CommRing A] [IsDomain A] [IsLocalRing A] {k : ℕ}
    (σ : Γ →* GL (Fin k) A) (g : Γ) (u : Fin k → FractionRing A) :
    overK σ g u = ((mat σ g).map (toFr A)).mulVec u := by
  simp [overK, mat, toFr, matRep, mapM]

theorem conj_of_isDecomp {Γ A : Type} [Group Γ] [CommRing A] [IsDomain A] [IsLocalRing A] {n r t : ℕ}
    (σ σ' : Γ →* GL (Fin n) A) (ρ ρ' : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ))
    (hP : ∃ Pm : GL (Fin n) (FractionRing A), ∀ g,
      (Pm : Matrix (Fin n) (Fin n) (FractionRing A)) * (mat σ g).map (toFr A) =
        (mat σ' g).map (toFr A) * (Pm : Matrix (Fin n) (Fin n) (FractionRing A)))
    (h : ∃ e, IsDecomp (t := t) σ ρ χ e) (h' : ∃ e, IsDecomp (t := t) σ' ρ' χ e) :
    ∃ Pm : GL (Fin r) (FractionRing A), ∀ g,
      (Pm : Matrix (Fin r) (Fin r) (FractionRing A)) * (mat ρ g).map (toFr A) =
        (mat ρ' g).map (toFr A) * (Pm : Matrix (Fin r) (Fin r) (FractionRing A)) := by
  obtain ⟨Pm, hPm⟩ := hP
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  let L : (Fin n → FractionRing A) ≃ₗ[FractionRing A] (Fin n → FractionRing A) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' (Pm : Matrix (Fin n) (Fin n) (FractionRing A)))
      (Matrix.toLin' ((Pm⁻¹ : GL (Fin n) (FractionRing A)) : Matrix (Fin n) (Fin n) (FractionRing A)))
      (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])
  have hL : ∀ g u, L (overK σ g u) = overK σ' g (L u) := by
    intro g u
    simp only [L, LinearEquiv.coe_ofLinearMap, Matrix.toLin'_apply, overK_apply, Matrix.mulVec_mulVec, hPm g]
  refine (cancel_fin (fun g => overK ρ g) (fun g => overK ρ' g) t
    (fun j g => toFr A ((χ (↑j + 1) g : Aˣ) : A)) ((e.symm.trans L).trans e') ?_).elim fun f hf => ?_
  · intro g v x
    have he1 := he g (e.symm (v, x))
    simp only [LinearEquiv.apply_symm_apply] at he1
    have h2 : e.symm (overK ρ g v, fun j => toFr A ((χ (↑j + 1) g : Aˣ) : A) * x j) = overK σ g (e.symm (v, x)) := by
      rw [← he1, LinearEquiv.symm_apply_apply]
    simp only [LinearEquiv.trans_apply]
    rw [h2, hL, he']
  · refine ⟨⟨LinearMap.toMatrix' (f : (Fin r → FractionRing A) →ₗ[FractionRing A] (Fin r → FractionRing A)),
      LinearMap.toMatrix' (f.symm : (Fin r → FractionRing A) →ₗ[FractionRing A] (Fin r → FractionRing A)), ?_, ?_⟩,
      fun g => ?_⟩
    · rw [← LinearMap.toMatrix'_comp]; simp
    · rw [← LinearMap.toMatrix'_comp]; simp
    · apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_toMatrix',
        Matrix.toLin'_apply, ← overK_apply, LinearEquiv.coe_coe]
      exact hf g v

theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))) (ρ ρ' : (N.X i → (GE N →* GL (Fin R.r) (N.O i)))) (π : N.X i), IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) (r π)) → (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r π g).map (toK N i) = (rO N i r' π g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) → (∃ e, IsDecomp (t := R.t) (r π) (ρ π) (N.chi i) e) → (∃ e, IsDecomp (t := R.t) (r' π) (ρ' π) (N.chi i) e) → (∃ Pm : GL (Fin R.r) (KK N i), ∀ g, (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i)) * (rhoO N i ρ π g).map (toK N i) = (rhoO N i ρ' π g).map (toK N i) * (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i))) := by
  intro R H what₂ N i r r' ρ ρ' π _ hP h h'
  exact conj_of_isDecomp (r π) (r' π) (ρ π) (ρ' π) (N.chi i) hP h h'

end GlobalTheory.CharCancel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjDualCharpolyOfSplitFrobeniusDense
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.CharDualDense

theorem t2_O0 {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) :
    T2Space (X.O0 i) :=
  (IsAdic.isHausdorff_iff (X.twistBaseCoefficientRing_isAdic i)).1 inferInstance

theorem finite_S0_conj {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) :
    ((X.S0 i : Set (PlE D.host)) ∪ {P | ∃ P' ∈ X.S0 i, IsConjPl D.host P P'}).Finite := by
  refine (X.S0 i).finite_toSet.union ?_
  refine ((X.S0 i).finite_toSet.biUnion (t := fun P' => {P | IsConjPl D.host P' P}) fun P' _ => ?_).subset ?_
  · exact (show ({P | IsConjPl D.host P' P} : Set (PlE D.host)).Subsingleton from
      fun a ha b hb => GlobalTheory.TwistDet.isConjPl_unique ha hb).finite
  · rintro P ⟨P', hP', hc⟩
    exact Set.mem_biUnion (x := P') hP' (GlobalTheory.TwistDet.isConjPl_symm hc)

theorem charDual_of_frobDual : ∀ (D : D7), GlobalTheory.TypeLeaf.FrobDense D → ∀ (i : D.ntw.Tw) (s : D.ntw.Sig i),
    FrobDual i s → CharDual i s := by
  intro D hF i s hFD g g' hg'
  haveI := t2_O0 D.ntw i
  have e : g' = GlobalTheory.TwistDet.cConj D.ntw g := by
    ext x
    rw [hg', GlobalTheory.TwistDet.cConj_apply]
  subst e
  refine GlobalTheory.TypeLeaf.charpoly_eq_of_dense (Gen.GE D.nd) (D.ntw.O0 i) D.R.r
    (fun g => Tdual i s (GlobalTheory.TwistDet.cConj D.ntw g))
    (fun g => ((((eps0 D.ntw i g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ D.R.t) • Tmat i s g)) _
    (hF _ (finite_S0_conj D.ntw i))
    ((GlobalTheory.PrimeToInertia.continuous_Tdual i s).comp (GlobalTheory.ResConjTriv.continuous_cConj D.ntw)) ?_ ?_ g
  · have h1 : Continuous fun g : Gen.GE D.nd => ((eps0 D.ntw i g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) :=
      (GlobalTheory.PrimeToInertia.continuous_algebraMap_padicInt _ (D.ntw.twistBaseCoefficientRing_isAdic i) (GlobalTheory.PrimeToInertia.l_mem i)).comp
        (Units.continuous_val.comp (continuous_cycZ D.host.E D.nd.Om (D.ntw.l i)))
    exact (h1.pow _).smul (GlobalTheory.PrimeToInertia.continuous_Tmat i s)
  · rintro σ ⟨w, hwT, hsp, B, hB, hσ⟩
    refine hFD w (fun h => hwT (Or.inl h)) hsp (fun P' hc h => hwT (Or.inr ⟨P', h, hc⟩)) B hB σ _ hσ
      (GlobalTheory.TwistDet.cConj_apply D.ntw σ)

end GlobalTheory.CharDualDense

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverPull
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

def Layer.pull {l : ℕ} [Fact l.Prime] {Γ Δ : Type} [Group Γ] [Group Δ] (j : Δ →* Γ) {a d' : ℕ} {L₀ : FinExt l}
    {Cl : Set (Γ →* GL (Fin a) (Om l))} {ρ' : Γ →* GL (Fin d') ℤ_[l]} (Y : Layer L₀ Cl ρ') :
    Layer L₀ ((fun ρ => ρ.comp j) '' Cl) (ρ'.comp j) where
  m := Y.m
  rep k := (Y.rep k).comp j
  mem k := ⟨Y.rep k, Y.mem k, rfl⟩
  L := Y.L
  le := Y.le
  rep_mem k g := Y.rep_mem k (j g)
  b := Y.b
  b_mem := Y.b_mem
  indep := Y.indep
  span := Y.span
  e := Y.e
  reads k := ⟨fun g => (Y.reads k).equi (j g), (Y.reads k).one⟩
  c := Y.c

def Tower.pull {l : ℕ} [Fact l.Prime] {Γ Δ : Type} [Group Γ] [Group Δ] (j : Δ →* Γ) {d : ℕ}
    {ρ : Γ →* GL (Fin d) ℤ_[l]} (T : Tower ρ) : Tower (ρ.comp j) where
  d' := T.d'
  ρ' n := (T.ρ' n).comp j
  Pi := T.Pi
  onto n := ⟨fun g => (T.onto n).equi (j g), (T.onto n).surj⟩
  f := T.f
  f_equi n g := T.f_equi n (j g)
  f_Pi := T.f_Pi

def Cover.pull {l : ℕ} [Fact l.Prime] {Γ Δ : Type} [Group Γ] [TopologicalSpace Γ] [Group Δ] [TopologicalSpace Δ]
    (j : Δ →* Γ) (hj : Continuous j) {a : ℕ} {L₀ : FinExt l} {r : Γ →* GL (Fin a) (Om l)}
    {Cl : Set (Γ →* GL (Fin a) (Om l))} (C : Cover L₀ r Cl) :
    Cover L₀ (r.comp j) ((fun ρ => ρ.comp j) '' Cl) where
  d := C.d
  ρ := C.ρ.comp j
  cont := C.cont.comp hj
  b := C.b
  e := C.e
  reads := ⟨fun g => C.reads.equi (j g), C.reads.one⟩
  tw := C.tw.pull j
  cont' n := (C.cont' n).comp hj
  lay n := (C.lay n).pull j
  unit := C.unit
  trace := C.trace

theorem cover_pull : ∀ (l : ℕ) [Fact l.Prime] (Γ Δ : Type) [Group Γ] [TopologicalSpace Γ] [Group Δ] [TopologicalSpace Δ] (j : Δ →* Γ), Continuous j → ∀ (a : ℕ) (L₀ : FinExt l) (r : Γ →* GL (Fin a) (Om l)) (Cl : Set (Γ →* GL (Fin a) (Om l))), Cover L₀ r Cl → Nonempty (Cover L₀ (r.comp j) ((fun ρ => ρ.comp j) '' Cl)) :=
  by
  intro _ _ _ _ _ _ _ _ j hj _ _ _ _ C
  exact ⟨C.pull j hj⟩

end GlobalTheory.BKLim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilteredComparisonCoordinates
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.DRFilCoord
open Module

theorem deRham_filtered_Ql (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (TT : LocTied l P AI)
    (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V) (hdR : IsDR (P.PD K) ρ) (a : ℤ) (y : V ⊗[ℚ_[l]] P.R.BdR)
    (hy : y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a) :
    ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR),
      (∀ i, d i ∈ DdR (P.PD K) ρ ∧ d i ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) (k i) ∧
        b i ∈ (P.PD K).Fil (a - k i)) ∧
      y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  let LL : FinExt l := ⟨⊥, inferInstance⟩
  let e : ↥LL.1 ≃ₐ[ℚ_[l]] ℚ_[l] := IntermediateField.botEquiv ℚ_[l] (Om l)
  letI iM : Module ↥LL.1 V := Module.compHom V (e : ↥LL.1 →+* ℚ_[l])
  haveI : IsScalarTower ℚ_[l] ↥LL.1 V := ⟨fun c x v => by
    show e (c • x) • v = c • (e x • v)
    have h1 := e.toLinearEquiv.map_smul c x
    simp only [AlgEquiv.toLinearEquiv_apply] at h1
    rw [h1, smul_eq_mul, mul_smul]⟩
  haveI : FiniteDimensional ↥LL.1 V := Module.Finite.of_restrictScalars_finite ℚ_[l] _ V
  let ρ' : Representation ↥LL.1 ↥(GK K) V :=
    { toFun := fun g =>
        { toFun := ρ g
          map_add' := fun u w => (ρ g).map_add u w
          map_smul' := fun c v => (ρ g).map_smul (e c) v }
      map_one' := by ext v; simp
      map_mul' := fun g h => by ext v; simp; rfl }
  have hV : finrank ↥LL.1 V = finrank ℚ_[l] V := by
    rw [← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 V, IntermediateField.finrank_bot, one_mul]
  have hR : ∀ g x, actVdR (P.PD K) ρ' g x = actVdR (P.PD K) ρ g x := fun g x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp [actVdR]; rfl
    | add u w hu hw => simp only [map_add, hu, hw]
  have hD : ∀ x, x ∈ DdR (P.PD K) ρ' ↔ x ∈ DdR (P.PD K) ρ := fun x => by
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hR]
  have hDd : (DdR (P.PD K) ρ').restrictScalars ℚ_[l] = DdR (P.PD K) ρ := by
    ext x
    rw [Submodule.restrictScalars_mem, hD]
  have hDr : finrank ↥LL.1 ↥(DdR (P.PD K) ρ') = finrank ℚ_[l] ↥(DdR (P.PD K) ρ) := by
    rw [← hDd, LinearEquiv.finrank_eq
      ((Submodule.restrictScalarsEquiv ℚ_[l] ↥LL.1 _ (DdR (P.PD K) ρ')).restrictScalars ℚ_[l]),
      ← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 ↥(DdR (P.PD K) ρ'), IntermediateField.finrank_bot, one_mul]
  have hDR' : IsDR (P.PD K) ρ' := by
    unfold IsDR at hdR ⊢
    rw [hDr, hV]; exact hdR
  obtain ⟨m, k, b, d, h, hy'⟩ := GlobalTheory.DRFil.deRham_filtered l P AI TT K LL V ρ' hDR' a y hy
  exact ⟨m, k, b, d, fun i => ⟨(hD _).1 (h i).1, (h i).2.1, (h i).2.2⟩, hy'⟩

theorem filtered_coords : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), IsDR (P.PD K) (qRep ρ) → ∀ (a : ℤ) (y : Fin d → P.R.BdR), (∀ i, y i ∈ (P.PD K).Fil a) → ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → P.R.BdR) (z : Fin m → Fin d → P.R.BdR), (∀ r, (∀ g : ↥(GK K), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (z r i)) = z r) ∧ (∀ i, z r i ∈ (P.PD K).Fil (k r)) ∧ b r ∈ (P.PD K).Fil (a - k r)) ∧ y = ∑ r, b r • z r := by
  intro l _ P AI TT K d ρ hdR a y hy
  let f : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (Fin d → P.R.BdR) :=
    (TensorProduct.piScalarRight ℚ_[l] ℚ_[l] P.R.BdR (Fin d)).toLinearMap ∘ₗ
      (TensorProduct.comm ℚ_[l] (Fin d → ℚ_[l]) P.R.BdR).toLinearMap
  have hf : ∀ (v : Fin d → ℚ_[l]) (β : P.R.BdR), f (v ⊗ₜ β) = fun i => v i • β := by
    intro v β; simp [f]
  have hfmul : ∀ (β : P.R.BdR) (x : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR),
      f (AlgebraTensorModule.map (LinearMap.id : (Fin d → ℚ_[l]) →ₗ[ℚ_[l]] (Fin d → ℚ_[l]))
        (LinearMap.mulLeft ℚ_[l] β) x) = β • f x := by
    intro β x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply, hf]
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
      ring
    | add u w hu hw => simp only [map_add, hu, hw, smul_add]
  have hfil : ∀ (c : ℤ) (x : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR),
      x ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) c → ∀ i, f x i ∈ (P.PD K).Fil c := by
    intro c x hx i
    refine GlobalTheory.DRFil.FilV_induction (P.PD K) (p := fun x => f x i ∈ (P.PD K).Fil c) ?_ ?_ ?_ hx
    · simp
    · intro v β hβ
      rw [hf]
      exact (((P.PD K).Fil c).restrictScalars ℚ_[l]).smul_mem (v i) hβ
    · intro x x' h h'
      rw [map_add]
      exact Submodule.add_mem _ h h'
  have hact : ∀ (g : ↥(GK K)) (x : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR),
      f (actVdR (P.PD K) (qRep ρ) g x) =
        (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ
          (fun i => P.actQdR (g : GQ l) (f x i)) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, Pi.zero_apply]; exact (Matrix.mulVec_zero _).symm
    | tmul v β =>
      have h1 : actVdR (P.PD K) (qRep ρ) g (v ⊗ₜ β) = qRep ρ g v ⊗ₜ P.actQdR (g : GQ l) β := by
        simp [actVdR, P.PD_actdR]
      rw [h1, hf, hf]
      funext i
      have hq : qRep ρ g v = ((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v := by
        simp [qRep, Matrix.toLin'_apply]
      rw [hq]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul]
      rfl
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, ← Matrix.mulVec_add]
      congr 1; funext i; simp
  let x : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR := ∑ i, Pi.single i (1 : ℚ_[l]) ⊗ₜ y i
  have hx : x ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) a :=
    Submodule.sum_mem _ fun i _ => GlobalTheory.DRFil.tmul_mem_FilV (P.PD K) (LL := ℚ_[l]) _ (hy i)
  have hfx : f x = y := by
    funext j
    simp [x, map_sum, hf, Pi.single_apply]
  obtain ⟨m, k, b, dd, h, e⟩ :=
    deRham_filtered_Ql l P AI TT K (Fin d → ℚ_[l]) (qRep ρ) hdR a x hx
  refine ⟨m, k, b, fun r => f (dd r), fun r => ⟨fun g => ?_, hfil _ _ (h r).2.1, (h r).2.2⟩, ?_⟩
  · have hg : actVdR (P.PD K) (qRep ρ) g (dd r) = dd r :=
      (GlobalTheory.DRFil.mem_DdR (P.PD K) (qRep ρ) _).1 (h r).1 g
    rw [← hact, hg]
  · rw [← hfx, e, map_sum]
    exact Finset.sum_congr rfl fun r _ => hfmul _ _

end GlobalTheory.DRFilCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaMemIdealPowOfMemPowSucc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem delta_pow_succ_mem_pow : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A),
    (l : A) ∈ J → ∀ (n : ℕ), ∀ x ∈ J ^ (n + 1), D.δ x ∈ J ^ n := by
  intro l hl A _ D J hlJ n
  have hl0 : 0 < l := hl.out.pos
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    have key : x ∈ J ^ (n + 1 + 1) ∧ D.δ x ∈ J ^ (n + 1) := by
      rw [pow_succ' J (n + 1)] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        refine ⟨?_, ?_⟩
        · rw [pow_succ' J (n + 1)]; exact Ideal.mul_mem_mul ha hb
        · rw [D.δ_mul]
          have h1 : a ^ l * D.δ b ∈ J ^ (n + 1) := by
            rw [pow_succ']; exact Ideal.mul_mem_mul (Ideal.pow_mem_of_mem J ha l hl0) (ih b hb)
          have h2 : b ^ l * D.δ a ∈ J ^ (n + 1) :=
            Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hb l hl0)
          have h3 : (l : A) * D.δ a * D.δ b ∈ J ^ (n + 1) := by
            rw [pow_succ']; exact Ideal.mul_mem_mul (Ideal.mul_mem_right _ _ hlJ) (ih b hb)
          exact Ideal.add_mem _ (Ideal.add_mem _ h1 h2) h3
      · rintro y z ⟨hy1, hy2⟩ ⟨hz1, hz2⟩
        refine ⟨Ideal.add_mem _ hy1 hz1, ?_⟩
        rw [D.δ_add]
        refine Ideal.sub_mem _ (Ideal.add_mem _ hy2 hz2) (Ideal.sum_mem _ fun k hk => ?_)
        have hk0 : 0 < k := (Finset.mem_Ioo.1 hk).1
        have hyk : y ^ k ∈ J ^ (n + 1) :=
          Ideal.pow_le_pow_right (Nat.le_succ _) (Ideal.pow_mem_of_mem _ hy1 k hk0)
        exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hyk)
    exact key.2

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetNeZeroOfLowestFormNeZeroPresentationStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_ne_zero_of_lowestForm_ne_zero_presentation : ∀ (A B : Type) [CommRing A] [CommRing B] (π : B →+* A) (x y : B) (μ : Type) [Fintype μ] (a a' : ℕ) (Φ' : Matrix (Fin a') (Fin a') B) (u t : μ → Fin a' → B) (η : μ → B) (Φ : Matrix (Fin a) (Fin a) A) (E : Matrix (Fin a) (Fin a') A) (U : μ → Fin a → A) (k : μ → A) (l₀ : Fin a), Function.Surjective π → (∀ b, π b = 0 → b ∈ Ideal.span {x, y}) → π x = 0 → π y = 0 → x * x = 0 → y ^ Fintype.card μ = 0 → (∀ f, x * y ^ (Fintype.card μ - 1) * f = 0 → π f = 0) → (∀ j, π (η j) = 1) → (∀ j, x • u j - (y * η j) • t j ∈ what₂ Φ') → what₂ E ⊔ (what₂ (Φ'.map π) ⊔ what₂ (fun j c => π (t j c))) = ⊤ → (∀ b, (Φ * E) b ∈ what₂ (Φ'.map π) ⊔ what₂ (fun j c => π (t j c))) → (∀ j, (fun c => π (u j c)) - Matrix.vecMul (U j) E ∈ what₂ (Φ'.map π) ⊔ what₂ (fun j c => π (t j c))) → ∑ j, k j • (fun c => π (t j c)) ∈ what₂ (Φ'.map π) → ∑ j, k j * ∑ c, U j c * Φ.adjugate c l₀ ≠ 0 → Φ'.det ≠ 0 := by
  first | exact @GlobalTheory.LowDet.det_ne_zero | exact GlobalTheory.LowDet.det_ne_zero | (intros; apply GlobalTheory.LowDet.det_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicTopologicalBasisOfSpanOfStrictStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adicTopologicalBasis_of_span_of_strict : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (b : ι → A) (i₀ : ι), b i₀ = 1 → I.FG → IsAdicComplete I S → IsAdicComplete (I.map s) A → (∀ x : A, ∃ a : ι →₀ S, x - a.sum (fun i y => s y * b i) ∈ I.map s) → (∀ n : ℕ, ∃ m : ℕ, ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (I ^ m).map s → ∀ i, a i ∈ I ^ n) → ∃ TB : TopBasis s I ι, TB.b = b := by
  first | exact @GlobalTheory.BSP.exists_topBasis_of_span_of_strict | exact GlobalTheory.BSP.exists_topBasis_of_span_of_strict | (intros; apply GlobalTheory.BSP.exists_topBasis_of_span_of_strict <;> assumption)
end

