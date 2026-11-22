import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0589
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0590
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0515
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0516
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatAtConstOne
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.Mem.Chr GlobalTheory.LFun

namespace GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E]

theorem pLoc_conjFin_eq (c : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (c x)) (hv : ∀ x, Valued.v (s x) = Valued.v x) (x : Af E) :
    pLoc E w (conjFin c x) = s (pLoc E w x) := by
  have hw : ConjPl c w w := fun k => by
    have h1 : Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
      w.valuedAdicCompletion_eq_valuation' k
    have h2 : Valued.v (algebraMap E (w.adicCompletion E) (c k)) = w.valuation E (c k) :=
      w.valuedAdicCompletion_eq_valuation' _
    rw [← h1, ← h2, ← hs, hv]
  have key : ∀ (u : HeightOneSpectrum (𝓞 E)) (_ : w = u) (φ : u.adicCompletion E →+* w.adicCompletion E),
      Continuous φ → (∀ k : E, φ (algebraMap E _ k) = algebraMap E _ (c k)) → φ (pLoc E u x) = s (pLoc E w x) := by
    rintro _ rfl φ h1 h2
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer h1
      (continuous_of_valued_eq (w.valuedAdicCompletion_surjective E) s hv)
      (funext fun k => (h2 k).trans (hs k).symm)) _
  rw [pLoc_conjFin]
  exact key _ (eq_conjSrc hw) _ (conjLoc_spec c w).1 (conjLoc_spec c w).2.1

variable [IsCMField E]

theorem cT_cLoc {n : ℕ} (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) (g : UA E n) : cT s (cLoc w g).val * (cLoc w g).val = 1 := by
  have hg : cT (conjAd E) g.1.val * 1 * g.1.val = 1 := g.2
  rw [Matrix.mul_one] at hg
  have h := congrArg ((pLoc E w).comp (pFin E)).mapMatrix hg
  rw [map_mul, map_one] at h
  rw [← h]
  congr 1
  refine Matrix.ext fun i j => ?_
  exact (pLoc_conjFin_eq (IsCMField.complexConj E).toRingEquiv w s hs hv (pFin E (g.1.val j i))).symm

end GlobalTheory.UnitaryBC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleResidualPointDescendsCoefficientExten
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LiveDescent

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

theorem isLocalHom_of_nonunit {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B]
    [IsLocalRing B] (f : A →+* B) {a : A} (ha : a ≠ 0) (hf : f a ∈ IsLocalRing.maximalIdeal B) : IsLocalHom f := by
  have hne : (IsLocalRing.maximalIdeal B).comap f ≠ ⊥ := fun h => ha (by
    have : a ∈ (IsLocalRing.maximalIdeal B).comap f := hf
    rwa [h, Ideal.mem_bot] at this)
  have hm : ((IsLocalRing.maximalIdeal B).comap f).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  have he := IsLocalRing.eq_maximalIdeal hm
  refine ⟨fun x hx => ?_⟩
  by_contra h
  have : x ∈ (IsLocalRing.maximalIdeal B).comap f := by rw [he]; exact h
  exact this hx

theorem continuous_of_isLocalHom {A B : Type} [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [IsLocalRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (IsLocalRing.maximalIdeal A)) (hB : IsAdic (IsLocalRing.maximalIdeal B)) (f : A →+* B)
    [IsLocalHom f] : Continuous f := by
  have hm : Ideal.map f (IsLocalRing.maximalIdeal A) ≤ IsLocalRing.maximalIdeal B :=
    Ideal.map_le_iff_le_comap.2 fun x hx => map_nonunit f x hx
  refine continuous_of_continuousAt_zero f.toAddMonoidHom ?_
  intro s hs
  rw [map_zero] at hs
  obtain ⟨n, hn⟩ := (isAdic_iff.1 hB).2 s hs
  refine Filter.mem_map.2 (Filter.mem_of_superset (((isAdic_iff.1 hA).1 n).mem_nhds (Ideal.zero_mem _))
    fun x hx => hn ?_)
  have h1 : f x ∈ Ideal.map f (IsLocalRing.maximalIdeal A ^ n) := Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono hm n h1

theorem span_eq_top_of_map {ι k K : Type} [Field k] [Field K] (f : k →+* K) {r : ℕ}
    (M : ι → Matrix (Fin r) (Fin r) k) (h : Submodule.span K (Set.range fun g => (M g).map f) = ⊤) :
    Submodule.span k (Set.range M) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨l, hl0, hl⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  have hexp : ∀ Y : Matrix (Fin r) (Fin r) k, l Y = ∑ p, ∑ q, Y p q * l (Matrix.single p q 1) := by
    intro Y
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have key : ∀ Y : Matrix (Fin r) (Fin r) K, ∑ p, ∑ q, Y p q * f (l (Matrix.single p q 1)) = 0 := by
    intro Y
    have hY : Y ∈ Submodule.span K (Set.range fun g => (M g).map f) := h ▸ Submodule.mem_top
    induction hY using Submodule.span_induction with
    | mem Y hY =>
      obtain ⟨g, rfl⟩ := hY
      have h0 : l (M g) = 0 := hl (Submodule.subset_span ⟨g, rfl⟩)
      have := congrArg f ((hexp (M g)).symm.trans h0)
      simpa [map_sum] using this
    | zero => simp
    | add Y Z _ _ hY hZ => simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, hY, hZ, add_zero]
    | smul a Y _ hY => simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hY, mul_zero]
  apply hl0
  refine LinearMap.ext fun Y => ?_
  rw [hexp, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  have h1 := key (Matrix.single p q 1)
  rw [Finset.sum_eq_single p (fun a _ ha => by simp [Matrix.single_apply_of_row_ne (Ne.symm ha)]) (by simp),
    Finset.sum_eq_single q (fun a _ ha => by simp [Matrix.single_apply_of_col_ne _ _ (Ne.symm ha)]) (by simp)] at h1
  simp only [Matrix.single_apply_same, one_mul, map_eq_zero] at h1
  rw [h1, mul_zero]

theorem trace_of_isDecomp {Γ A : Type} [Group Γ] [CommRing A] [IsDomain A] [IsLocalRing A] {n r t : ℕ}
    (σ : Γ →* GL (Fin n) A) (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (h : ∃ e, IsDecomp (t := t) σ ρ χ e)
    (g : Γ) : (mat σ g).trace = (mat ρ g).trace + ∑ c : Fin t, ((χ ((c : ℕ) + 1) g : Aˣ) : A) := by
  obtain ⟨e, he⟩ := h
  apply IsFractionRing.injective A (FractionRing A)
  let d : Fin t → FractionRing A := fun c => toFr A ((χ ((c : ℕ) + 1) g : Aˣ) : A)
  have h1 : Matrix.toLin' ((mat σ g).map (toFr A)) =
      e.symm.conj ((Matrix.toLin' ((mat ρ g).map (toFr A))).prodMap (Matrix.toLin' (Matrix.diagonal d))) := by
    apply LinearMap.ext
    intro u
    apply e.injective
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm,
      LinearMap.prodMap_apply]
    refine (he g u).trans ?_
    ext c
    · rfl
    · simp [Matrix.mulVec_diagonal, d]
  have h2 := congrArg (LinearMap.trace _ _) h1
  rw [LinearMap.trace_conj', LinearMap.trace_prodMap', Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq,
    Matrix.trace_toLin'_eq, Matrix.trace_diagonal] at h2
  rw [map_add, map_sum, AddMonoidHom.map_trace, AddMonoidHom.map_trace]
  exact h2

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem charZero_O (N : NData R H what₂) (A : NAut N) (i : N.Loc) : CharZero (N.O i) :=
  (iotaO N A i).charZero

theorem l_mem_maximalIdeal (N : NData R H what₂) (A : NAut N) (i : N.Loc) :
    ((N.l i : ℕ) : N.O i) ∈ IsLocalRing.maximalIdeal (N.O i) := by
  have hinj : Function.Injective (algebraMap ℤ_[N.l i] (N.O i)) := by
    intro x y h
    have hx := A.iotaQ_alg i x
    rw [h, A.iotaQ_alg i y] at hx
    exact (Subtype.ext ((algebraMap ℚ_[N.l i] (Qbar (N.l i))).injective hx)).symm
  have : FaithfulSMul ℤ_[N.l i] (N.O i) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have h : ((N.l i : ℕ) : ℤ_[N.l i]) ∈ IsLocalRing.maximalIdeal ℤ_[N.l i] := PadicInt.p_nonunit
  have := map_nonunit (algebraMap ℤ_[N.l i] (N.O i)) _ h
  rwa [map_natCast] at this

variable {N₀ N₁ : NData R H what₂} {A₀ : NAut N₀} {A₁ : NAut N₁} {i₀ : N₀.Loc} {i₁ : N₁.Loc}

theorem isLocalHom_φ (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) : IsLocalHom a.φ := by
  have := charZero_O N₀ A₀ i₀
  have hl : (N₁.l i₁).Prime := Fact.out
  refine isLocalHom_of_nonunit a.φ (a := ((N₁.l i₁ : ℕ) : N₀.O i₀)) (Nat.cast_ne_zero.2 hl.ne_zero) ?_
  rw [map_natCast]
  exact l_mem_maximalIdeal N₁ A₁ i₁

theorem continuous_φ (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) : Continuous a.φ :=
  haveI := isLocalHom_φ a
  continuous_of_isLocalHom (N₀.O_adic i₀) (N₁.O_adic i₁) a.φ

theorem trace_eq (hC : GlobalTheory.TwSys.Cheb) (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) (x : N₁.X i₁)
    (r₀ : GE N₀ →* GL (Fin R.nV) (N₀.O i₀)) (r₁ : GE N₁ →* GL (Fin R.nV) (N₁.O i₁))
    (h₀ : IsHeckeGalois N₀ i₀ (a.e x) r₀) (h₁ : IsHeckeGalois N₁ i₁ x r₁) (g : GE N₁) :
    a.φ (mat r₀ (a.γ g)).trace = (mat r₁ g).trace := by
  haveI := (N₁.O_complete i₁).toIsHausdorff
  haveI : T2Space (N₁.O i₁) := (N₁.O_adic i₁).isHausdorff_iff.1 inferInstance
  refine congrFun (GlobalTheory.BlockComplement.AE.eq_of_continuous (N := N₁) hC
    (f := fun g => a.φ (mat r₀ (a.γ g)).trace) (f' := fun g => (mat r₁ g).trace)
    ((continuous_φ a).comp (h₀.1.matrix_trace.comp a.γ_cont)) h₁.1.matrix_trace ?_) g
  filter_upwards [GlobalTheory.BlockComplement.eventually_out i₁] with w h hw B σ hB hσ
  obtain ⟨B₀, hB₀, hσ₀⟩ := (a.frob w σ).1 ⟨B, hB, hσ⟩
  have e₀ := h₀.2.2 w ((a.out w).1 (h hw)) B₀ _ hB₀ hσ₀
  have e₁ := h₁.2.2 w (h hw) B σ hB hσ
  rw [GlobalTheory.CoefDuty.Model.heckePol_map a x w (h hw), ← e₀, ← Matrix.charpoly_map] at e₁
  rw [AddMonoidHom.map_trace, Matrix.trace_eq_neg_charpoly_nextCoeff, Matrix.trace_eq_neg_charpoly_nextCoeff, e₁]

end Record

theorem live_of_locExt : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N₀ N₁ : NData R H what₂) (A₀ : NAut N₀) (A₁ : NAut N₁) (i₀ : N₀.Loc) (i₁ : N₁.Loc), LocExt N₀ N₁ A₀ A₁ i₀ i₁ → (∃ r, GoodR N₀ i₀ r) → ZDecomp N₀ i₀ → Live N₁ i₁ → Live N₀ i₀ := by
  rintro hC R H what₂ N₀ N₁ A₀ A₁ i₀ i₁ a ⟨r₀, hr₀⟩ hZ ⟨π, hπ, r, ρ, hr, hd, habs⟩
  have hπ₀ := (a.Z π).1 hπ
  obtain ⟨ρ₀, hd₀⟩ := hZ _ hπ₀ _ (hr₀ _)
  refine ⟨_, hπ₀, _, ρ₀, hr₀ _, hd₀, ?_⟩
  have htr : ∀ g, a.φ (mat ρ₀ (a.γ g)).trace = (mat ρ g).trace := by
    intro g
    have h := trace_eq hC a π _ r (hr₀ _) hr g
    rw [trace_of_isDecomp _ _ _ hd₀, trace_of_isDecomp _ _ _ hd, map_add, map_sum,
      Finset.sum_congr rfl fun (c : Fin R.t) _ => a.chi ((c : ℕ) + 1) (by omega) c.2 g] at h
    exact add_right_cancel h
  haveI := isLocalHom_φ a
  have hpos := pos_of_absIrrSub _ habs
  haveI : Nonempty (Fin R.r) := ⟨⟨0, hpos⟩⟩
  refine absIrrSub_of_span_eq_top hpos _ (span_eq_top_of_map (IsLocalRing.ResidueField.map a.φ) _ ?_)
  have h := span_eq_top_of_trace_eq
    ((mapRep (IsLocalRing.ResidueField.map a.φ) (mapRep (IsLocalRing.residue (N₀.O i₀)) ρ₀)).comp a.γ.toMonoidHom)
    (mapRep (IsLocalRing.residue (N₁.O i₁)) ρ) (fun g => ?_) (GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ habs)
  · rw [eq_top_iff, ← h]
    refine Submodule.span_mono ?_
    rintro _ ⟨g, rfl⟩
    exact ⟨a.γ g, (mat_mapRep _ _ _).symm⟩
  · change (mat (mapRep (IsLocalRing.ResidueField.map a.φ) (mapRep (IsLocalRing.residue (N₀.O i₀)) ρ₀))
      (a.γ g)).trace = _
    rw [mat_mapRep, mat_mapRep, mat_mapRep, ← AddMonoidHom.map_trace, ← AddMonoidHom.map_trace,
      ← AddMonoidHom.map_trace, ← htr, IsLocalRing.ResidueField.map_residue]

end GlobalTheory.LiveDescent

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDROfLinksStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDR_of_links' : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (F₀ : Frame bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r) → (∀ n, (F n).IsDR) → F₀.IsDR := by
  first | (exact @GlobalTheory.BKLim.isDR_of_links) | (exact GlobalTheory.BKLim.isDR_of_links) | (intros; apply GlobalTheory.BKLim.isDR_of_links  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsExactTripleBreuilKisinOfShortExactLattices
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKExact

theorem det_mul_eq_sum_fun' {R : Type*} [CommRing R] {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m]
    [DecidableEq m] (A : Matrix ι m R) (B : Matrix m ι R) :
    (A * B).det = ∑ f : ι → m, (∏ β, B (f β) β) * (A.submatrix id f).det := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.prod_mul_distrib, Matrix.submatrix_apply, id]
  ring

def selCols {R : Type*} [CommRing R] {m n : Type*} [DecidableEq n] (s : m → n) : Matrix n m R :=
  fun k i => if s i = k then (1 : R) else 0

theorem mul_selCols {R : Type*} [CommRing R] {m n : Type*} [Fintype n] [DecidableEq n] (N : Matrix m n R)
    (s : m → n) : N * (selCols (R := R) s) = N.submatrix id s := by
  ext i j
  rw [Matrix.mul_apply]
  simp [selCols]

theorem exists_right_of_minor {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (N : Matrix m n (A O K)) (s : m → n) :
    ∃ Y : Matrix n m K⟦X⟧, (∀ i j, Y i j ∈ A O K) ∧
      N.map (A O K).val * Y = ((N.submatrix id s).det : K⟦X⟧) • (1 : Matrix m m K⟦X⟧) := by
  refine ⟨(selCols (R := A O K) s * (N.submatrix id s).adjugate).map (A O K).val, fun i j => (_ : A O K).2, ?_⟩
  have h1 : N.map (A O K).val * (selCols (R := A O K) s * (N.submatrix id s).adjugate).map (A O K).val =
      (N * (selCols (R := A O K) s * (N.submatrix id s).adjugate)).map (A O K).val := by
    simp only [Matrix.map_mul]
  rw [h1, ← Matrix.mul_assoc, mul_selCols, Matrix.mul_adjugate]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem exists_right {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (M : Matrix m n (ZMod a → A O K))
    (Z : Matrix n m (OW l O)) (hZ : M.map (fun x => inclO l O (ϖ.iTot t K x)) * Z = 1) (τ : ZMod a) :
    ∃ (Y : Matrix n m K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ g ∈ A O K ∧ (∃ k, ‖coeff k g‖ = 1) ∧
      (Matrix.of fun i j => (M i j τ : K⟦X⟧)) * Y = g • (1 : Matrix m m K⟦X⟧) := by
  let φ : (ZMod a → A O K) →+* OW l O := (inclO l O).toRingHom.comp (ϖ.iTot t K).toRingHom
  have h1 := congrArg Matrix.det hZ
  rw [Matrix.det_one, det_mul_eq_sum_fun'] at h1
  have h2 : ∀ f : m → n, ((M.map fun x => inclO l O (ϖ.iTot t K x)).submatrix id f).det =
      inclO l O (ϖ.iTot t K (M.submatrix id f).det) := fun f => by
    exact (RingHom.map_det φ (M.submatrix id f)).symm
  simp only [h2] at h1
  obtain ⟨f, k, hk⟩ := GlobalTheory.T.exists_unit_coeff_wittTilt_relation t ϖ (fun f => (M.submatrix id f).det) _ h1 τ
  let N : Matrix m n (A O K) := fun i j => M i j τ
  have h3 : (M.submatrix id f).det τ = (N.submatrix id f).det :=
    RingHom.map_det (Pi.evalRingHom (fun _ : ZMod a => A O K) τ) (M.submatrix id f)
  obtain ⟨Y, hY, hNY⟩ := exists_right_of_minor N f
  refine ⟨Y, _, hY, (N.submatrix id f).det.2, ⟨k, ?_⟩, hNY⟩
  rw [← h3]
  exact hk

theorem isExactTriple_of_isSESLat_gen {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type} [Group G] [TopologicalSpace G]
    {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]
    {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ}
    {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂}
    {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : BK.Hom P₀ P₁} {H : BK.Hom P₁ P₂}
    (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H) : IsExactTriple F H := by
  obtain ⟨⟨Z, hZ⟩, ⟨Yw, hYw⟩⟩ := GlobalTheory.T.phiModuleHom_shortExact_split_wittTilt_alt t ϖ hS hF hH
  have hex := GlobalTheory.T.tame_setting_group_action_compat t ϖ hS hF hH
  let φ : (ZMod a → A O K) →+* OW l O := (inclO l O).toRingHom.comp (ϖ.iTot t K).toRingHom
  have hφ : Function.Injective φ := inclO_injective.comp (ϖ.iTot_injective t K)
  let ψ : ZMod a → (ZMod a → A O K) →+* K⟦X⟧ := fun τ =>
    (A O K).val.toRingHom.comp (Pi.evalRingHom (fun _ : ZMod a => A O K) τ)
  have extPi : ∀ {m n : Type} (M N : Matrix m n (ZMod a → A O K)),
      (∀ τ, M.map (ψ τ) = N.map (ψ τ)) → M = N := fun M N h => by
    funext i j τ
    exact Subtype.ext (congrFun₂ (h τ) i j)
  let Ht : Matrix μ κ (ZMod a → A O K) := fun i j τ => ⟨H.mat τ i j, H.mem τ i j⟩
  let Ft : Matrix κ ι (ZMod a → A O K) := fun i j τ => ⟨F.mat τ i j, F.mem τ i j⟩
  have hHr : ∀ τ, ∃ (Y : Matrix κ μ K⟦X⟧) (c : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧
      c ∈ A O K ∧ (∃ k, ‖coeff k c‖ = 1) ∧ H.mat τ * Y = c • (1 : Matrix μ μ K⟦X⟧) :=
    fun τ => exists_right t ϖ Ht Z hZ τ
  have hFl : ∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (c : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧
      c ∈ A O K ∧ (∃ k, ‖coeff k c‖ = 1) ∧ Y * F.mat τ = c • (1 : Matrix ι ι K⟦X⟧) := by
    intro τ
    have hT : Ftᵀ.map (fun x => inclO l O (ϖ.iTot t K x)) * Ywᵀ = 1 := by
      rw [Matrix.transpose_map, ← Matrix.transpose_mul]
      exact (congrArg Matrix.transpose hYw).trans Matrix.transpose_one
    obtain ⟨Y, c, hY, hc, hk, h⟩ := exists_right t ϖ Ftᵀ Ywᵀ hT τ
    refine ⟨Yᵀ, c, fun i j => hY j i, hc, hk, ?_⟩
    have h1 := congrArg Matrix.transpose h
    rw [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_one] at h1
    exact h1
  choose YH cH hYH hcH hkH hHY using hHr
  choose YF cF hYF hcF hkF hFY using hFl
  have hne : ∀ {c : K⟦X⟧}, (∃ k, ‖coeff k c‖ = 1) → c ≠ 0 := by
    rintro c ⟨k, hk⟩ rfl
    simp at hk
  refine ⟨?_, ?_, ?_⟩
  · intro v hv hFv
    funext τ
    have h1 : cF τ • v τ = 0 := by
      have h2 := congrArg (fun x => YF τ *ᵥ x τ) hFv
      simp only [Hom.app_apply, Matrix.mulVec_mulVec, hFY, Matrix.smul_mulVec, Matrix.one_mulVec,
        Pi.zero_apply, Matrix.mulVec_zero] at h2
      exact h2
    exact (smul_eq_zero.1 h1).resolve_left (hne (hkF τ))
  · intro v hv
    constructor
    · intro hHv
      refine (GlobalTheory.T.finiteLength_coker_of_surjective_mod_uniformizer O K l e a ι κ P₀ P₁ F).2 (fun τ => ⟨YF τ, cF τ, hYF τ, hkF τ, hFY τ⟩) v hv
        (∏ τ, cF τ) (prod_mem fun τ _ => hcF τ) (Finset.prod_ne_zero_iff.2 fun τ _ => hne (hkF τ)) ?_
      let Yt : Matrix ι κ (ZMod a → A O K) := fun i j τ => ⟨YF τ i j, hYF τ i j⟩
      let gt : ZMod a → A O K := fun τ => ⟨cF τ, hcF τ⟩
      let vt : κ → ZMod a → A O K := fun i τ => ⟨v τ i, mem_tot.1 hv τ i⟩
      have hYFt : Yt * Ft = Matrix.diagonal fun _ => gt := by
        refine extPi _ _ fun τ => ?_
        rw [Matrix.map_mul, Matrix.diagonal_map (map_zero _)]
        exact (hFY τ).trans (Matrix.smul_one_eq_diagonal _)
      have hv' : toW t ϖ P₁ ⟨v, mem_ME_of_mem_M hv⟩ = fun i => φ (vt i) :=
        funext fun i => ϖ.iW_of_mem t K (vt i)
      have h0 : homW t ϖ H (toW t ϖ P₁ ⟨v, mem_ME_of_mem_M hv⟩) = 0 := by
        rw [homW_toW]
        have : (⟨H.app v, H.app_mem_Mext (le_away _ _) (mem_ME_of_mem_M hv)⟩ : ME P₂) = 0 :=
          Subtype.ext hHv
        rw [this, map_zero]
      obtain ⟨w, hw⟩ := hex _ h0
      rw [homW_apply, hv'] at hw
      change Ft.map φ *ᵥ w = fun i => φ (vt i) at hw
      have h1 : (Ft * Yt).map φ *ᵥ (fun i => φ (vt i)) = φ gt • (fun i => φ (vt i)) := by
        rw [← hw, Matrix.map_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc,
          show Yt.map φ * Ft.map φ = (Yt * Ft).map φ from (Matrix.map_mul).symm, hYFt,
          Matrix.diagonal_map (map_zero _), ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
          Matrix.smul_mulVec]
      have h2 : (Ft * Yt) *ᵥ vt = gt • vt := by
        funext i
        apply hφ
        rw [RingHom.map_mulVec]
        refine (congrFun h1 i).trans ?_
        show φ gt * φ (vt i) = φ (gt * vt i)
        rw [map_mul]
      have hkey : ∀ τ, F.mat τ *ᵥ (YF τ *ᵥ v τ) = cF τ • v τ := fun τ => by
        funext i
        have := congrArg (ψ τ) (congrFun h2 i)
        rw [RingHom.map_mulVec, Matrix.map_mul] at this
        rw [Matrix.mulVec_mulVec]
        exact this.trans (map_mul (ψ τ) gt (vt i))
      refine ⟨fun τ => (∏ σ ∈ Finset.univ.erase τ, cF σ) • (YF τ *ᵥ v τ), mem_tot.2 fun τ i => ?_, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
        exact mul_mem (prod_mem fun σ _ => hcF σ)
          (sum_mem fun j _ => mul_mem (hYF τ i j) (mem_tot.1 hv τ j))
      · change F.app _ = _
        funext τ
        rw [Hom.app_apply, Matrix.mulVec_smul, hkey, smul_smul,
          Finset.prod_erase_mul _ _ (Finset.mem_univ τ)]
        rfl
    · rintro ⟨w, hw, rfl⟩
      have hlat : ∀ z, latW g (latW f z) = 0 := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul w x =>
          have h0 : ((g.f.restrictScalars O).restrict g.T_le) (((f.f.restrictScalars O).restrict f.T_le) x) = 0 :=
            Subtype.ext ((hS.2.2.2.1 (f.f x)).2 ⟨x, rfl⟩)
          simp only [latW, TensorProduct.map_tmul, LinearMap.id_apply, h0, TensorProduct.tmul_zero]
        | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
      have hW : ∀ x, homW t ϖ H (homW t ϖ F x) = 0 := fun x =>
        I₂.j.injective (by rw [hH, hF, hlat, map_zero])
      have hM : (Ht * Ft).map φ = 0 := by
        ext i j
        have := congrFun (hW (Pi.single j 1)) i
        rw [homW_apply, homW_apply, Matrix.mulVec_mulVec] at this
        simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply] at this
        rw [Matrix.map_mul]
        exact this
      have hz : Ht * Ft = 0 := Matrix.map_injective hφ (hM.trans (Matrix.map_zero _ (map_zero φ)).symm)
      have hHF : ∀ τ, H.mat τ * F.mat τ = 0 := fun τ => by
        have := congrArg (fun M => M.map (ψ τ)) hz
        simp only [Matrix.map_mul, Matrix.map_zero _ (map_zero (ψ τ))] at this
        exact this
      change H.app (F.app w) = 0
      funext τ
      rw [Hom.app_apply, Hom.app_apply, Matrix.mulVec_mulVec, hHF τ, Matrix.zero_mulVec]
      rfl
  · exact (GlobalTheory.T.finiteLength_coker_of_surjective_mod_uniformizer O K l e a κ μ P₁ P₂ H).1 fun τ => ⟨YH τ, cH τ, hYH τ, hkH τ, hHY τ⟩

theorem isExactTriple_of_isSESLat : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (μ : Type) [Fintype μ] [DecidableEq μ] (P₀ : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (P₁ : PhiMod ↥(OL LL) ↥LL.1 l e a κ) (P₂ : PhiMod ↥(OL LL) ↥LL.1 l e a μ) (T₀ T₁ T₂ : QLat LL) (I₀ : Ident (thetaW a LL) ϖ P₀ T₀) (I₁ : Ident (thetaW a LL) ϖ P₁ T₁) (I₂ : Ident (thetaW a LL) ϖ P₂ T₂) (f : LatHom T₀.L T₁.L) (g : LatHom T₁.L T₂.L) (F : GlobalTheory.BK.Hom P₀ P₁) (G : GlobalTheory.BK.Hom P₁ P₂), IsSESLat (Qp := ℚ_[l]) f g → IsMapOf I₀ I₁ f F → IsMapOf I₁ I₂ g G → IsExactTriple F G := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ κ _ _ μ _ _ P₀ P₁ P₂ T₀ T₁ T₂ I₀ I₁ I₂ f g F G hS hF hG
  exact isExactTriple_of_isSESLat_gen (thetaW a LL) ϖ hS hF hG

end GlobalTheory.BKExact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodEmptyIff
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG

namespace GlobalTheory.RSNonvan

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def lfac {a b : ℕ} (σ : CG E a) (σ' : CG E b) (s : ℂ) (w : HeightOneSpectrum (𝓞 E)) : ℂ :=
  locL (Ideal.absNorm w.asIdeal) (sat σ w) ((sat σ' w).map (Units.map (starRingEnd ℂ).toMonoidHom)) s

def IsGood (T : Finset (HeightOneSpectrum (𝓞 E))) : Prop :=
  (∀ w ∈ T, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ T) ∧
    ∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w

def dcoef {a b : ℕ} (σ : CG E a) (σ' : CG E b) (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) : ℝ :=
  ‖(((sat σ w).map (fun α : ℂˣ => (α : ℂ)) + (sat σ' w).map (fun α : ℂˣ => (α : ℂ))).map (· ^ (r + 1))).sum‖ ^ 2 /
    ((r : ℝ) + 1)

def dexp (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) : ℝ := ((r : ℝ) + 1) * Real.log (Ideal.absNorm w.asIdeal)

theorem dcoef_nonneg {a b : ℕ} (σ : CG E a) (σ' : CG E b) (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) :
    0 ≤ dcoef σ σ' w r := div_nonneg (sq_nonneg _) (by positivity)

theorem dexp_nonneg (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) : 0 ≤ dexp w r :=
  mul_nonneg (by positivity) (Real.log_nonneg (by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm w
    exact_mod_cast this.le))

end GlobalTheory.RSNonvan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralOrIsIntegralInvInFieldFactorStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_or_isIntegral_inv_in_fieldFactor : ∀ (K : UQ) (B : InvAlg K) (f y z : B.A), IsIdempotentElem f → (∀ w, f * w ≠ 0 → ∃ v, f * w * v = f) → f * y * z = f → IsIntegral K.O (f * y) ∨ IsIntegral K.O (f * z) := by
  first | exact @GlobalTheory.UnitLemma.Desc.isIntegral_or_isIntegral_of_fieldFactor | exact GlobalTheory.UnitLemma.Desc.isIntegral_or_isIntegral_of_fieldFactor | (intros; apply GlobalTheory.UnitLemma.Desc.isIntegral_or_isIntegral_of_fieldFactor <;> assumption)
end

