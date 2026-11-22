import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0744
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0745
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0305
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0071
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdelicExtensionOfAlgebraicWeightDefiniteUn
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix Pointwise

namespace GlobalTheory.WeightRealExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem dense_rat_fin : Dense ((ratU E n : Set (UA E n)) * (finU E n : Set (UA E n))) := by
  intro g
  obtain ⟨k, hk, x, hx, rfl⟩ := GlobalTheory.DefU.exists_finU_mul_infU E n g
  rw [GlobalTheory.DefU.fin_mul_inf hk hx]
  have hc : Continuous (· * k : UA E n → UA E n) := continuous_mul_const k
  refine closure_mono ?_
    (image_closure_subset_closure_image hc ⟨x, GlobalTheory.DefiniteDense.mem_closure_rat_fin x hx, rfl⟩)
  rintro _ ⟨_, ⟨γ, hγ, k', hk', rfl⟩, rfl⟩
  exact ⟨γ, hγ, k' * k, (finU E n).mul_mem hk' hk, (mul_assoc _ _ _).symm⟩

theorem mem_rationalGL_of_unitaryGroupGram_unitGram (γ : UA E n) (γ₀ : GL (Fin n) E) (h : γ.1 = ratGL E n γ₀) : γ₀ ∈ GQ0 E n := by
  have h0 : Formalism.UG.cT (conjAd E) (γ.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * γ.1 = 1 := γ.2
  rw [mul_one, h] at h0
  have e : Formalism.UG.cT (conjAd E) ((γ₀ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E))) =
      (conjT (IsCMField.complexConj E : E →+* E) (γ₀ : Matrix (Fin n) (Fin n) E)).map (algebraMap E (Ad E)) := by
    ext i j
    simp [Formalism.UG.cT, conjT, conjAd_algebraMap]
  change Formalism.UG.cT (conjAd E) ((γ₀ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E))) *
      (γ₀ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E)) = 1 at h0
  rw [e, ← Matrix.map_mul, ← Matrix.map_one (algebraMap E (Ad E)) (map_zero _) (map_one _)] at h0
  have h1 := Matrix.map_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 E) E) h0
  exact mul_eq_one_comm.1 h1

def ratPt : GQ0 E n →* GQ E n where
  toFun γ := ⟨⟨GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : E →+* AL E) γ.1, by
      have h0 : (γ.1 : Matrix (Fin n) (Fin n) E) * conjT (IsCMField.complexConj E : E →+* E) γ.1 = 1 := γ.2
      have e : conjT (conjAL E) ((γ.1 : Matrix (Fin n) (Fin n) E).map
          (Algebra.TensorProduct.includeLeftRingHom : E →+* AL E)) =
          (conjT (IsCMField.complexConj E : E →+* E) (γ.1 : Matrix (Fin n) (Fin n) E)).map
            (Algebra.TensorProduct.includeLeftRingHom : E →+* AL E) := by
        ext i j
        simp [conjT, conjAL]
      change (γ.1 : Matrix (Fin n) (Fin n) E).map (Algebra.TensorProduct.includeLeftRingHom : E →+* AL E) *
        conjT (conjAL E) ((γ.1 : Matrix (Fin n) (Fin n) E).map
          (Algebra.TensorProduct.includeLeftRingHom : E →+* AL E)) = 1
      rw [e, ← Matrix.map_mul, h0, Matrix.map_one _ (map_zero _) (map_one _)]⟩,
    Subgroup.mem_subgroupOf.2 ⟨γ.1, γ.2, rfl⟩⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' x y := Subtype.ext (Subtype.ext (map_mul _ _ _))

def polyMat {ι : Type} (P : ι → ι → MvPolynomial ((E →+* ℂ) × Fin n × Fin n) ℂ) (g : UA E n) : Matrix ι ι ℂ :=
  fun i j => MvPolynomial.eval (fun p => coord p.1 ((cInf g : Matrix (Fin n) (Fin n) (Cinf E)) p.2.1 p.2.2)) (P i j)

theorem polyMat_congr {ι : Type} (P : ι → ι → MvPolynomial ((E →+* ℂ) × Fin n × Fin n) ℂ) {g h : UA E n}
    (e : cInf g = cInf h) : polyMat P g = polyMat P h := by
  unfold polyMat
  rw [e]

theorem polyMat_rat {ι : Type} (P : ι → ι → MvPolynomial ((E →+* ℂ) × Fin n × Fin n) ℂ) (γ : UA E n)
    (γ₀ : GL (Fin n) E) (h : γ.1 = ratGL E n γ₀) :
    polyMat P γ = fun i j =>
      MvPolynomial.eval (fun p => p.1 ((γ₀ : Matrix (Fin n) (Fin n) E) p.2.1 p.2.2)) (P i j) := by
  funext i j
  unfold polyMat
  congr 2
  funext p
  rw [← coord_algebraMap p.1]
  congr 1
  change pInf E ((γ.1 : Matrix (Fin n) (Fin n) (Ad E)) p.2.1 p.2.2) = _
  rw [h]
  rfl

omit [NumberField E] [IsCMField E] in

theorem continuous_coord' (τ : E →+* ℂ) : Continuous (coord τ) := by
  unfold coord
  split_ifs
  · exact continuous_apply _
  · exact Complex.continuous_conj.comp (continuous_apply _)

theorem continuous_pInf' : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_polyMat {ι : Type} (P : ι → ι → MvPolynomial ((E →+* ℂ) × Fin n × Fin n) ℂ) :
    Continuous (polyMat P) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (MvPolynomial.continuous_eval (P i j)).comp (continuous_pi fun p => ?_)
  refine (continuous_coord' p.1).comp (continuous_pInf'.comp
    (f := fun g : UA E n => (g.1 : Matrix (Fin n) (Fin n) (Ad E)) p.2.1 p.2.2) ?_)
  exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _

theorem exists_unitaryRationalMatrix_of_mem_definiteUnitaryRational {γ : UA E n} (hγ : γ ∈ ratU E n) : ∃ γ₀ : GQ0 E n, γ.1 = ratGL E n γ₀.1 := by
  obtain ⟨γ₀, hγ₀⟩ := Subgroup.mem_subgroupOf.1 hγ
  exact ⟨⟨γ₀, mem_rationalGL_of_unitaryGroupGram_unitGram γ γ₀ hγ₀.symm⟩, hγ₀.symm⟩

theorem mul_of_dense {G M : Type} [Mul G] [TopologicalSpace G] [ContinuousMul G] [Mul M] [TopologicalSpace M]
    [ContinuousMul M] [T2Space M] {D : Set G} (hD : Dense D) (f : G → M) (hf : Continuous f)
    (h : ∀ x ∈ D, ∀ y ∈ D, f (x * y) = f x * f y) (x y : G) : f (x * y) = f x * f y := by
  have hcl : IsClosed {z : G × G | f (z.1 * z.2) = f z.1 * f z.2} :=
    isClosed_eq (hf.comp (continuous_fst.mul continuous_snd))
      ((hf.comp continuous_fst).mul (hf.comp continuous_snd))
  exact hcl.closure_subset_iff.2 (fun z hz => h z.1 hz.1 z.2 hz.2) ((hD.prod hD) (x, y))

theorem mul_of_rat {M : Type} [Mul M] [TopologicalSpace M] [ContinuousMul M] [T2Space M] (f : UA E n → M)
    (hf : Continuous f) (hi : ∀ g h, cInf g = cInf h → f g = f h)
    (h : ∀ x ∈ ratU E n, ∀ y ∈ ratU E n, f (x * y) = f x * f y) : ∀ x y, f (x * y) = f x * f y := by
  refine mul_of_dense dense_rat_fin f hf fun x hx y hy => ?_
  obtain ⟨γ, hγ, k, hk, hx⟩ := Set.mem_mul.1 hx
  obtain ⟨δ, hδ, l, hl, hy⟩ := Set.mem_mul.1 hy
  have hk' : cInf k = 1 := hk
  have hl' : cInf l = 1 := hl
  have e1 : cInf x = cInf γ := by rw [← hx, map_mul, hk', mul_one]
  have e2 : cInf y = cInf δ := by rw [← hy, map_mul, hl', mul_one]
  rw [hi x γ e1, hi y δ e2, hi (x * y) (γ * δ) (by rw [map_mul, map_mul, e1, e2]), h γ hγ δ hδ]

theorem exists_extension : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n), ∃ R : UA L n →* Module.End ℂ a.W, (∀ k ∈ finU L n, R k = 1) ∧ (∀ (γ : UA L n) (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ → (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → R γ = a.ρ γQ) ∧ ∀ (v : a.W) (μ : Module.Dual ℂ a.W), Continuous fun g : UA L n => μ (R g v) := by
  intro L _ _ _ n a
  obtain ⟨_, ι, _, _, b, P, hP⟩ := a.alg
  have hrat : ∀ (γ : UA L n) (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ →
      (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom →
      polyMat P γ = LinearMap.toMatrix b b (a.ρ γQ) := fun γ γQ γ₀ h1 h2 =>
    (polyMat_rat P γ γ₀ h1).trans (hP γQ γ₀ h2).symm
  have hrat' : ∀ (γ : UA L n) (γ₀ : GQ0 L n), γ.1 = ratGL L n γ₀.1 →
      polyMat P γ = LinearMap.toMatrix b b (a.ρ (ratPt γ₀)) := fun γ γ₀ h => hrat γ _ γ₀.1 h rfl
  have hone : polyMat P 1 = 1 := by
    rw [hrat' 1 1 (map_one (ratGL L n)).symm, map_one, map_one, LinearMap.toMatrix_one]
  have hmul : ∀ g h : UA L n, polyMat P (g * h) = polyMat P g * polyMat P h := by
    refine mul_of_rat (polyMat P) (continuous_polyMat P) (fun _ _ => polyMat_congr P) fun γ hγ δ hδ => ?_
    obtain ⟨γ₀, hγ₀⟩ := exists_unitaryRationalMatrix_of_mem_definiteUnitaryRational hγ
    obtain ⟨δ₀, hδ₀⟩ := exists_unitaryRationalMatrix_of_mem_definiteUnitaryRational hδ
    have e : (γ * δ).1 = ratGL L n (γ₀ * δ₀).1 := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, hγ₀, hδ₀]
    rw [hrat' γ γ₀ hγ₀, hrat' δ δ₀ hδ₀, hrat' (γ * δ) (γ₀ * δ₀) e, map_mul, map_mul, LinearMap.toMatrix_mul]
  refine ⟨⟨⟨fun g => Matrix.toLin b b (polyMat P g), ?_⟩, fun g h => ?_⟩, fun k hk => ?_, fun γ γQ γ₀ h1 h2 => ?_,
    fun v μ => ?_⟩
  · rw [hone, Matrix.toLin_one]
    rfl
  · change Matrix.toLin b b (polyMat P (g * h)) = _
    rw [hmul, Matrix.toLin_mul b b b]
    rfl
  · change Matrix.toLin b b (polyMat P k) = 1
    rw [polyMat_congr P (g := k) (h := 1) ((show cInf k = 1 from hk).trans (map_one _).symm), hone, Matrix.toLin_one]
    rfl
  · change Matrix.toLin b b (polyMat P γ) = _
    rw [hrat γ γQ γ₀ h1 h2, Matrix.toLin_toMatrix]
  · change Continuous fun g : UA L n => μ (Matrix.toLin b b (polyMat P g) v)
    have hc := continuous_polyMat P
    simp only [Matrix.toLin_apply, map_sum, map_smul, smul_eq_mul]
    refine continuous_finset_sum _ fun j _ => Continuous.mul ?_ continuous_const
    exact (continuous_apply j).comp (hc.matrix_mulVec continuous_const)

end GlobalTheory.WeightRealExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChange
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.GalIsoBC

def Good (D : D7) (i : D.nd.Loc) (r : ℕ) (p : ∀ w, D.naut.LP w)
    (m : (D.host.E →+* ℂ) → Multiset ℂ) : Prop :=
  ∃ ρ : GE D.nd →* GL (Fin r) (Qbar (D.nd.l i)), (SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧
    (∀ w, D.naut.wdOf i ρ w = p w) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧
      ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) =
        m ((D.naut.iotaQC i).toRingHom.comp τ))

theorem good_congr {D : D7} {i : D.nd.Loc} {r r' : ℕ} {p p' : ∀ w, D.naut.LP w}
    {m m' : (D.host.E →+* ℂ) → Multiset ℂ} (hr : r = r') (hp : ∀ w, p w = p' w) (hm : ∀ τ, m τ = m' τ)
    (h : Good D i r p m) : Good D i r' p' m' := by
  subst hr
  have e1 : p = p' := funext hp
  have e2 : m = m' := funext hm
  subst e1; subst e2; exact h

theorem good_sum {D : D7} (h0 : SumRepresentations.tie0 D) {i : D.nd.Loc} {a b : ℕ} {p q : ∀ w, D.naut.LP w}
    {m m' : (D.host.E →+* ℂ) → Multiset ℂ} (ha : Good D i a p m) (hb : Good D i b q m') :
    Good D i (a + b) (fun w => D.naut.lpSum (p w) (q w)) (fun τ => m τ + m' τ) := by
  obtain ⟨ρ, hρ⟩ := ha
  obtain ⟨ρ', hρ'⟩ := hb
  exact GlobalTheory.T.galois_rep_multiset_jumps D h0 i a b ρ ρ' p q m m' hρ hρ'

theorem good_fold {D : D7} (h0 : SumRepresentations.tie0 D) {i : D.nd.Loc} {β : Type*} (r : β → ℕ)
    (f : β → ∀ w, D.naut.LP w) (g : β → (D.host.E →+* ℂ) → Multiset ℂ) :
    ∀ L : List β, L ≠ [] → (∀ x ∈ L, Good D i (r x) (f x) (g x)) →
      Good D i (L.map r).sum (fun w => L.foldr (fun x acc => D.naut.lpSum (f x w) acc) (D.naut.lpZero w))
        (fun τ => (L.map fun x => g x τ).sum)
  | [], h, _ => (h rfl).elim
  | [x], _, hx => by
      refine good_congr ?_ ?_ ?_ (hx x (List.mem_singleton_self x))
      · simp
      · intro w; simp [D.naut.lpSum_zero]
      · intro τ; simp
  | x :: y :: L, _, hx => by
      have ih := good_fold h0 r f g (y :: L) (List.cons_ne_nil _ _)
        (fun z hz => hx z (List.mem_cons_of_mem _ hz))
      have := good_sum h0 (hx x List.mem_cons_self) ih
      refine good_congr ?_ ?_ ?_ this
      · simp only [List.map_cons, List.sum_cons]
      · intro w; simp only [List.foldr_cons]
      · intro τ; simp only [List.map_cons, List.sum_cons]

theorem lpTw_lpZero (D : D7) (w : PlE D.host) (s : ℝ) : D.naut.lpTw (D.naut.lpZero w) s = D.naut.lpZero w := by
  have hu : D.naut.unr (D.naut.lpTw (D.naut.lpZero w) s) := (D.naut.unr_tw _ s).2 (D.naut.lpZero_unr w)
  have e3 : D.naut.frobEig (D.naut.lpTw (D.naut.lpZero w) s) = D.naut.frobEig (D.naut.lpZero w) := by
    rw [D.naut.frobEig_tw _ s (D.naut.lpZero_unr w), D.naut.frobEig_zero]; simp
  rw [D.naut.unr_eq_lpUnr _ hu, e3, ← D.naut.unr_eq_lpUnr _ (D.naut.lpZero_unr w)]

theorem lpTw_foldr (D : D7) (w : PlE D.host) {β : Type*} (f : β → D.naut.LP w) (s : ℝ) :
    ∀ L : List β, D.naut.lpTw (L.foldr (fun x acc => D.naut.lpSum (f x) acc) (D.naut.lpZero w)) s =
      L.foldr (fun x acc => D.naut.lpSum (D.naut.lpTw (f x) s) acc) (D.naut.lpZero w)
  | [] => lpTw_lpZero D w s
  | x :: L => by
      simp only [List.foldr_cons]
      rw [D.naut.lpTw_sum, lpTw_foldr D w f s L]

theorem map_list_sum {α γ : Type*} (h : α → γ) :
    ∀ L : List (Multiset α), L.sum.map h = (L.map fun x => x.map h).sum
  | [] => by simp
  | x :: L => by simp [Multiset.map_add, map_list_sum h L]

theorem le_list_sum {α : Type*} {x : Multiset α} : ∀ {L : List (Multiset α)}, x ∈ L → x ≤ L.sum
  | [], hx => by simp at hx
  | y :: L, hx => by
      rw [List.sum_cons]
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Multiset.le_add_right _ _
      · exact le_trans (le_list_sum hx) (Multiset.le_add_left _ _)

end GlobalTheory.GalIsoBC

namespace GlobalTheory.GalIsoBC

theorem flatMap_single {γ : Type*} (f : ℕ → γ) : ∀ l : List ℕ, List.flatMap (fun a => [f a]) l = l.map f
  | [] => rfl
  | a :: l => by simp [List.flatMap_cons, flatMap_single f l]

theorem spehLoc_eq (D : D7) (p : Formalism.BasicNotions.Part D.naut.CG) (w : PlE D.host) :
    spehLoc D.nd D.naut p w = (List.range p.d).foldr (fun (k : ℕ) acc =>
      D.naut.lpSum (D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - (k : ℝ))) acc) (D.naut.lpZero w) := by
  unfold spehLoc
  simp only [bind, pure]
  rw [flatMap_single (fun a : ℕ => (a : ℝ)), List.foldr_map]

theorem isoInf_eq (D : D7) (Pa : List (Formalism.BasicNotions.Part D.naut.CG)) (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut Pa τ = (Pa.map fun p => ((List.range p.d).map fun k : ℕ =>
        (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (k : ℂ)))).sum).sum := by
  unfold isoInf
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [bind, pure]
  rw [flatMap_single (fun a : ℕ => (a : ℂ)), List.map_map]
  rfl

end GlobalTheory.GalIsoBC

namespace GlobalTheory.GalIsoBC

theorem good_part (D : D7) (h0 : SumRepresentations.tie0 D) (h2 : SumRepresentations.adm2 D) (i : D.nd.Loc) (P : D.naut.AV i)
    (Pa : List (Formalism.BasicNotions.Part D.naut.CG)) (hinf : ∀ τ, isoInf D.nd D.naut Pa τ = D.naut.infWt i τ)
    (p : Formalism.BasicNotions.Part D.naut.CG) (hp : p ∈ Pa) (ha : 1 ≤ p.a) (hd : 1 ≤ p.d) (hc : D.naut.csd p.π) :
    Good D i (p.a * p.d) (fun w => D.naut.lpTw (spehLoc D.nd D.naut p w) ((1 - (D.R.nV : ℝ)) / 2))
      (fun τ => (((List.range p.d).map fun k : ℕ =>
        (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (k : ℂ)))).sum).map
          (fun z => -z + ((D.R.nV : ℂ) - 1) / 2)) := by
  have hreg := GlobalTheory.T.infWt_nodup_and_half_integral D i P
  set e : ℕ → ℤ := fun k => (p.d : ℤ) - 2 * k - D.R.nV with he
  have hne : List.range p.d ≠ [] := by
    rw [Ne, List.range_eq_nil]; omega
  have hpiece : ∀ k ∈ List.range p.d, Good D i p.a (fun w => D.naut.lpTw (D.naut.locG p.π w) ((e k : ℝ) / 2))
      (fun τ => (D.naut.infG p.π τ).map (fun z => -(z + (e k : ℂ) / 2))) := by
    intro k hk
    refine GlobalTheory.T.exists_galois_rep_twist D h0 h2 i p.a ha p.π (e k) hc ?_
    intro τ
    have hS : (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (k : ℂ))) ≤ D.naut.infWt i τ := by
      rw [← hinf τ, isoInf_eq]
      refine le_trans (le_list_sum (List.mem_map_of_mem (f := fun k : ℕ =>
        (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (k : ℂ)))) hk)) ?_
      exact le_list_sum (List.mem_map_of_mem (f := fun p : Formalism.BasicNotions.Part D.naut.CG => ((List.range p.d).map fun k : ℕ =>
        (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (k : ℂ)))).sum) hp)
    refine ⟨Multiset.Nodup.of_map _ (Multiset.nodup_of_le hS (hreg τ).1), ?_⟩
    intro z hz
    obtain ⟨m, hm⟩ := (hreg τ).2 _ (Multiset.mem_of_le hS (Multiset.mem_map_of_mem _ hz))
    refine ⟨m, ?_⟩
    have hm' : z = (m : ℂ) + ((D.R.nV : ℂ) - 1) / 2 - (((p.d : ℂ) - 1) / 2 - k) := by
      rw [← hm]; ring
    rw [hm', he]; push_cast; ring
  have hf := good_fold h0 (fun _ : ℕ => p.a)
    (fun k w => D.naut.lpTw (D.naut.locG p.π w) ((e k : ℝ) / 2))
    (fun k τ => (D.naut.infG p.π τ).map (fun z => -(z + (e k : ℂ) / 2))) (List.range p.d) hne hpiece
  refine good_congr ?_ ?_ ?_ hf
  · simp [mul_comm]
  · intro w
    have h1 := lpTw_foldr D w (fun k : ℕ => D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - (k : ℝ)))
      ((1 - (D.R.nV : ℝ)) / 2) (List.range p.d)
    beta_reduce at h1
    rw [spehLoc_eq, h1]
    congr 1
    funext k acc
    rw [D.naut.lpTw_add, he]
    congr 2
    push_cast; ring
  · intro τ
    rw [map_list_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    simp only [Function.comp_apply, Multiset.map_map]
    congr 1
    funext z
    simp only [Function.comp_apply, he]
    push_cast; ring

theorem galRep_isobaric : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm2 D → ∀ (i : D.nd.Loc) (P : D.naut.AV i) (Pa : List (Formalism.BasicNotions.Part D.naut.CG)), IsBCV D.nd D.naut i P Pa → ∃ ρ : GE D.nd →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), (SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧ (∀ w, D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) = (D.naut.infWt i ((D.naut.iotaQC i).toRingHom.comp τ)).map (fun z => -z + ((D.R.nV : ℂ) - 1) / 2)) := by
  intro D h0 h2 i P Pa hB
  obtain ⟨hparts, -, hrank, -, -, hinf⟩ := hB
  have hne : Pa ≠ [] := by
    rintro rfl
    have ht := D.R.t_odd.pos
    simp [rankIso, Ranks.nV] at hrank
    omega
  have hf := good_fold h0 (fun p : Formalism.BasicNotions.Part D.naut.CG => p.a * p.d)
    (fun p w => D.naut.lpTw (spehLoc D.nd D.naut p w) ((1 - (D.R.nV : ℝ)) / 2))
    (fun p τ => (((List.range p.d).map fun k : ℕ =>
        (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (k : ℂ)))).sum).map
          (fun z => -z + ((D.R.nV : ℂ) - 1) / 2)) Pa hne
    (fun p hp => good_part D h0 h2 i P Pa hinf p hp (hparts p hp).1 (hparts p hp).2.1 (hparts p hp).2.2)
  have hg : Good D i D.R.nV (fun w => D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2))
      (fun τ => (D.naut.infWt i τ).map (fun z => -z + ((D.R.nV : ℂ) - 1) / 2)) := by
    refine good_congr ?_ ?_ ?_ hf
    · exact hrank
    · intro w
      exact (lpTw_foldr D w (fun p : Formalism.BasicNotions.Part D.naut.CG => spehLoc D.nd D.naut p w) _ Pa).symm
    · intro τ
      rw [← hinf τ, isoInf_eq, map_list_sum, List.map_map]
      rfl
  exact hg

end GlobalTheory.GalIsoBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHighestWeightVectorDualWeylModuleUpperStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_highest_weight_vector_dualWeylModule_upper : ∀ (n : ℕ) (lam : DomWeight n), ∃ v : nablaSq ℂ n lam, v ≠ 0 ∧ ∀ B : GL (Fin n) ℂ, (B : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id → GlobalTheory.Branching.sqRep ℂ n lam B v = (∏ i, ((B : Matrix (Fin n) (Fin n) ℂ) i i) ^ (lam.w i)) • v := by
  first | exact @GlobalTheory.HwUpper.exists_hw_upper | exact GlobalTheory.HwUpper.exists_hw_upper | (intros; apply GlobalTheory.HwUpper.exists_hw_upper <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLadicCoefficientFieldEmbeddingsComplex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.EmbExt

open Cardinal

theorem exists_extend_of_countable {A K : Type} [Field A] [Field K] [Algebra A K] [Countable A]
    (hK : #K ≤ 𝔠) (φ : A →+* ℂ) : ∃ ψ : K →+* ℂ, ∀ a, ψ (algebraMap A K a) = φ a := by
  letI : Algebra A ℂ := φ.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis A K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis A ℂ
  have hA : #A ≤ ℵ₀ := Cardinal.mk_le_aleph0
  have hC : ℵ₀ < #ℂ := by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  have ht' : #ℂ = #t := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hA hC
  have hst : #s ≤ #t := by
    rw [← ht', Cardinal.mk_complex]
    exact (Cardinal.mk_le_mk_of_subset (Set.subset_univ _)).trans (by simpa using hK)
  obtain ⟨f⟩ := hst
  have hw : AlgebraicIndependent A (fun x : s => ((f x : t) : ℂ)) :=
    ht.1.comp (fun x => f x) f.injective
  let S := Algebra.adjoin A (Set.range ((↑) : s → K))
  let g : S →ₐ[A] ℂ := (MvPolynomial.aeval (fun x : s => ((f x : t) : ℂ))).comp hs.1.aevalEquiv.symm.toAlgHom
  have hg : Function.Injective g := (show Function.Injective (MvPolynomial.aeval (fun x : s => ((f x : t) : ℂ))) from hw).comp
    hs.1.aevalEquiv.symm.injective
  letI : Algebra S ℂ := g.toRingHom.toAlgebra
  haveI : Module.IsTorsionFree S ℂ := Module.isTorsionFree_iff_algebraMap_injective.2 hg
  haveI : Module.IsTorsionFree S K := Module.isTorsionFree_iff_algebraMap_injective.2 Subtype.val_injective
  haveI : Algebra.IsAlgebraic S K := hs.isAlgebraic
  let ψ : K →ₐ[S] ℂ := IsAlgClosed.lift
  refine ⟨ψ.toRingHom, fun a => ?_⟩
  have h1 : algebraMap A K a = algebraMap S K (algebraMap A S a) := rfl
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, ψ.commutes]
  exact g.commutes a

end GlobalTheory.EmbExt

namespace GlobalTheory.EmbExt

theorem isAlgebraic_rat_of_isIntegral_int {R F : Type} [CommRing R] [Field F] [CharZero F] (g : R →+* F)
    {y : R} (hy : IsIntegral ℤ y) : IsAlgebraic ℚ (g y) := by
  obtain ⟨p, hp, hev⟩ := hy
  refine ⟨p.map (Int.castRingHom ℚ), (hp.map _).ne_zero, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  have h : (algebraMap ℚ F).comp (Int.castRingHom ℚ) = g.comp (algebraMap ℤ R) := RingHom.ext_int _ _
  rw [h, ← Polynomial.hom_eval₂, hev, map_zero]

end GlobalTheory.EmbExt

namespace GlobalTheory.EmbExt

theorem exists_side_embeddings : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (f0 : ∀ i, Bool → (FractionRing (X.O0 i) →+* ℂ)), (∀ i b x, f0 i b ((if b then X.emb0 i else X.emb0b i) x) = embLL0 D x) → (∀ i k, Cardinal.mk (FractionRing (X.Ok i k)) ≤ Cardinal.continuum) → ∃ (e : ∀ i, Bool → (FractionRing (X.O i) →+* ℂ)) (ek : ∀ i, Bool → ∀ k, FractionRing (X.Ok i k) →+* ℂ), (∀ i b x, e i b (sideEmb X i b x) = embLL0 D x) ∧ (∀ i b k (x : X.O i), ek i b k (algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) (algebraMap (X.O i) (X.Ok i k) x)) = e i b (algebraMap (X.O i) (FractionRing (X.O i)) x)) ∧ (∀ i b (y : X.O0 i), IsIntegral ℤ y → e i b (algebraMap (X.O i) (FractionRing (X.O i)) (algebraMap (X.O0 i) (X.O i) y)) = f0 i b (algebraMap (X.O0 i) (FractionRing (X.O0 i)) y)) := by
  intro D N X f0 hf0 hcard
  have hcz : ∀ i, CharZero (FractionRing (X.O0 i)) := fun i => charZero_of_injective_ringHom (X.emb0 i).injective
  have key : ∀ i b, ∃ e : FractionRing (X.O i) →+* ℂ, letI := hcz i; ∀ z : FractionRing (X.O0 i), IsAlgebraic ℚ z →
      e (IsFractionRing.map (A := X.O0 i) (B := X.O i) (K := FractionRing (X.O0 i))
        (L := FractionRing (X.O i)) (X.O_inj i) z) = f0 i b z := by
    intro i b
    letI := hcz i
    let A := algebraicClosure ℚ (FractionRing (X.O0 i))
    haveI : Algebra.IsAlgebraic ℚ A := ⟨fun a => IntermediateField.isAlgebraic_iff.2 (mem_algebraicClosure_iff.1 a.2)⟩
    haveI : Countable A := by
      rw [← Cardinal.mk_le_aleph0_iff]
      exact (Algebra.IsAlgebraic.cardinalMk_le_max ℚ A).trans (by simp)
    let m := IsFractionRing.map (A := X.O0 i) (B := X.O i) (K := FractionRing (X.O0 i))
        (L := FractionRing (X.O i)) (X.O_inj i)
    letI : Algebra A (FractionRing (X.O i)) := (m.comp (algebraMap A (FractionRing (X.O0 i)))).toAlgebra
    have hK : Cardinal.mk (FractionRing (X.O i)) ≤ Cardinal.continuum :=
      (Cardinal.mk_le_of_injective (IsFractionRing.map (A := X.O i) (B := X.Ok i 0) (K := FractionRing (X.O i))
        (L := FractionRing (X.Ok i 0)) (X.Ok_inj i 0)).injective).trans (hcard i 0)
    obtain ⟨ψ, hψ⟩ := exists_extend_of_countable hK ((f0 i b).comp (algebraMap A (FractionRing (X.O0 i))))
    refine ⟨ψ, fun z hz => ?_⟩
    have hzA : z ∈ A := mem_algebraicClosure_iff.2 hz
    exact hψ ⟨z, hzA⟩
  choose e he using key
  have keyk : ∀ i b k, ∃ ek : FractionRing (X.Ok i k) →+* ℂ, ∀ x : X.O i,
      ek (algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) (algebraMap (X.O i) (X.Ok i k) x)) =
        e i b (algebraMap (X.O i) (FractionRing (X.O i)) x) := by
    intro i b k
    letI : Algebra (X.O i) ℂ := ((e i b).comp (algebraMap (X.O i) (FractionRing (X.O i)))).toAlgebra
    haveI : Module.IsTorsionFree (X.O i) ℂ := Module.isTorsionFree_iff_algebraMap_injective.2
      ((e i b).injective.comp (IsFractionRing.injective (X.O i) (FractionRing (X.O i))))
    haveI : Module.IsTorsionFree (X.O i) (FractionRing (X.Ok i k)) := by
      refine Module.isTorsionFree_iff_algebraMap_injective.2 ?_
      rw [IsScalarTower.algebraMap_eq (X.O i) (X.Ok i k) (FractionRing (X.Ok i k))]
      exact (IsFractionRing.injective (X.Ok i k) (FractionRing (X.Ok i k))).comp (X.Ok_inj i k)
    haveI := X.Ok_fin i k
    haveI : Algebra.IsAlgebraic (X.O i) (X.Ok i k) := Algebra.IsIntegral.isAlgebraic
    haveI : Algebra.IsAlgebraic (X.O i) (FractionRing (X.Ok i k)) :=
      (IsFractionRing.isAlgebraic_iff' (X.O i) (X.Ok i k) (FractionRing (X.Ok i k))).1 inferInstance
    let ψ : FractionRing (X.Ok i k) →ₐ[X.O i] ℂ := IsAlgClosed.lift
    refine ⟨ψ.toRingHom, fun x => ?_⟩
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← IsScalarTower.algebraMap_apply, ψ.commutes]
    rfl
  choose ek hek using keyk
  refine ⟨e, ek, fun i b x => ?_, hek, fun i b y hy => ?_⟩
  · letI := hcz i
    have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
    have h2 : IsAlgebraic ℚ ((if b then X.emb0 i else X.emb0b i) x) :=
      hx.algHom ((if b then X.emb0 i else X.emb0b i).toRatAlgHom)
    rw [← hf0 i b x, ← he i b _ h2]
    rfl
  · letI := hcz i
    have h2 : IsAlgebraic ℚ (algebraMap (X.O0 i) (FractionRing (X.O0 i)) y) :=
      isAlgebraic_rat_of_isIntegral_int _ hy
    rw [← he i b _ h2]
    simp [IsFractionRing.map, IsLocalization.map_eq]

end GlobalTheory.EmbExt
end

