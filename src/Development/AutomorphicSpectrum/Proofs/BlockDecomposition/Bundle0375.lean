import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0367
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0202
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0371
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0061
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0226
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

theorem map_lev {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (g : GL (Fin r) R × GL (Fin s) R) :
    GeneralLinearGroup.map p (lev R r s g) = lev S r s (GeneralLinearGroup.map p g.1, GeneralLinearGroup.map p g.2) := by
  ext i j
  change p ((lev R r s g : Matrix _ _ R) i j) = (lev S r s _ : Matrix _ _ S) i j
  rw [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.val_emb₂]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp [Matrix.fromBlocks] <;> rfl

theorem lev_infGL (y₁ : GL (Fin r) (Cinf E)) (y₂ : GL (Fin s) (Cinf E)) :
    lev (Ad E) r s (infGL E r y₁, infGL E s y₂) = infGL E (r + s) (lev (Cinf E) r s (y₁, y₂)) := by
  refine ga_ext ?_ ?_
  · rw [map_lev, pInf_infGL, pInf_infGL, pInf_infGL]
  · rw [map_lev, pFin_infGL, pFin_infGL, pFin_infGL]
    exact map_one _

theorem lev_finGL (k₁ : GL (Fin r) (Af E)) (k₂ : GL (Fin s) (Af E)) :
    lev (Ad E) r s (finGL E r k₁, finGL E s k₂) = finGL E (r + s) (lev (Af E) r s (k₁, k₂)) := by
  refine ga_ext ?_ ?_
  · rw [map_lev, pInf_finGL, pInf_finGL, pInf_finGL]
    exact map_one _
  · rw [map_lev, pFin_finGL, pFin_finGL, pFin_finGL]

theorem star_val_lev (k : Kinf E r) :
    star ((lev (Cinf E) r s (Unitary.toUnits k, 1) : GL _ _) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) =
      ((lev (Cinf E) r s (Unitary.toUnits (star k), 1) : GL _ _) : Matrix _ _ _) := by
  rw [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.val_emb₂, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex,
    Matrix.fromBlocks_conjTranspose]
  simp
  rfl

theorem lev_mem_unitary (k : Kinf E r) :
    ((lev (Cinf E) r s (Unitary.toUnits k, 1) : GL _ _) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) ∈
      Matrix.unitaryGroup (Fin (r + s)) (Cinf E) := by
  rw [Matrix.mem_unitaryGroup_iff, star_val_lev, ← Units.val_mul, ← map_mul, Prod.mk_mul_mk, ← map_mul,
    Unitary.mul_star_self, map_one, one_mul, Prod.mk_one_one, map_one, Units.val_one]

variable (E r s) in

def levK : Kinf E r →* Kinf E (r + s) where
  toFun k := ⟨_, lev_mem_unitary (s := s) k⟩
  map_one' := Subtype.ext (by
    change Units.val (lev (Cinf E) r s (Unitary.toUnits 1, 1)) = 1
    rw [map_one, Prod.mk_one_one, map_one, Units.val_one])
  map_mul' k k' := Subtype.ext (by
    change Units.val (lev (Cinf E) r s (Unitary.toUnits (k * k'), 1)) =
      Units.val (lev (Cinf E) r s (Unitary.toUnits k, 1)) * Units.val (lev (Cinf E) r s (Unitary.toUnits k', 1))
    rw [← Units.val_mul, ← map_mul, Prod.mk_mul_mk, map_mul, one_mul])

theorem toUnits_levK (k : Kinf E r) :
    Unitary.toUnits (levK E r s k) = lev (Cinf E) r s (Unitary.toUnits k, 1) := Units.ext rfl

theorem infGL_levK (k : Kinf E r) :
    infGL E (r + s) (Unitary.toUnits (levK E r s k)) = lev (Ad E) r s (infGL E r (Unitary.toUnits k), 1) := by
  rw [toUnits_levK, ← lev_infGL, map_one]

theorem continuous_levK : Continuous (levK E r s) := by
  refine Continuous.subtype_mk ?_ _
  have e : (fun k : Kinf E r => ((lev (Cinf E) r s (Unitary.toUnits k, 1) : GL _ _) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E))) =
      fun k : Kinf E r => Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
        (Matrix.fromBlocks k.1 0 0 1) := by
    funext k
    rw [GlobalTheory.SmGL.val_emb₂]
    rfl
  change Continuous (fun k : Kinf E r => ((lev (Cinf E) r s (Unitary.toUnits k, 1) : GL _ _) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)))
  rw [e]
  exact (continuous_subtype_val.matrix_fromBlocks continuous_const continuous_const continuous_const).matrix_reindex _ _

variable (s) in

def levelOne (L : Subgroup (GL (Fin (r + s)) (Af E))) (t : GL (Fin (r + s)) (Af E)) : Subgroup (GL (Fin r) (Af E)) :=
  L.comap ((MulAut.conj t⁻¹).toMonoidHom.comp ((lev (Af E) r s).comp (MonoidHom.inl _ _)))

theorem mem_levelOne {L : Subgroup (GL (Fin (r + s)) (Af E))} {t : GL (Fin (r + s)) (Af E)} {k : GL (Fin r) (Af E)} :
    k ∈ levelOne s L t ↔ t⁻¹ * lev (Af E) r s (k, 1) * t ∈ L := by
  simp [levelOne, MulAut.conj_apply]

theorem continuous_lev (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] : Continuous (lev R r s) :=
  (GlobalTheory.SmGL.continuous_leviEmb R _).comp (GlobalTheory.SmGL.continuous_leviTwo R)

theorem isOpen_levelOne {L : Subgroup (GL (Fin (r + s)) (Af E))} (hL : IsOpen (L : Set (GL (Fin (r + s)) (Af E))))
    (t : GL (Fin (r + s)) (Af E)) : IsOpen (levelOne s L t : Set (GL (Fin r) (Af E))) := by
  have hc : Continuous fun k : GL (Fin r) (Af E) => t⁻¹ * lev (Af E) r s (k, 1) * t :=
    (continuous_const.mul ((continuous_lev (Af E)).comp (continuous_id.prodMk continuous_const))).mul continuous_const
  convert hL.preimage hc using 1
  ext k
  exact mem_levelOne

end GlobalTheory.CompanionTheory.CTFin.Slice1
end

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

theorem lev_mul_one (m₁ x : GA E r) (m₂ : GA E s) :
    lev (Ad E) r s (m₁ * x, m₂) = lev (Ad E) r s (m₁, m₂) * lev (Ad E) r s (x, 1) := by
  rw [← map_mul, Prod.mk_mul_mk, mul_one]

theorem lev_infGL_right (g : GA E r) (y : GL (Fin r) (Cinf E)) (m₂ : GA E s) (t : GL (Fin (r + s)) (Af E))
    (c : GL (Fin (r + s)) (Cinf E)) :
    lev (Ad E) r s (g * infGL E r y, m₂) * finGL E (r + s) t * infGL E (r + s) c =
      lev (Ad E) r s (g, m₂) * finGL E (r + s) t * infGL E (r + s) (lev (Cinf E) r s (y, 1) * c) := by
  have e1 : lev (Ad E) r s (infGL E r y, 1) = infGL E (r + s) (lev (Cinf E) r s (y, 1)) := by
    rw [← lev_infGL, map_one]
  rw [lev_mul_one, e1, map_mul (infGL E (r + s)), mul_assoc (lev (Ad E) r s (g, m₂)) (infGL E (r + s) _),
    infGL_comm]
  simp only [mul_assoc]

theorem lev_finGL_right (m : GA E r) (k : GL (Fin r) (Af E)) (m₂ : GA E s) (t : GL (Fin (r + s)) (Af E))
    (c : GL (Fin (r + s)) (Cinf E)) :
    lev (Ad E) r s (m * finGL E r k, m₂) * finGL E (r + s) t * infGL E (r + s) c =
      lev (Ad E) r s (m, m₂) * finGL E (r + s) t * infGL E (r + s) c *
        finGL E (r + s) (t⁻¹ * lev (Af E) r s (k, 1) * t) := by
  have e1 : lev (Ad E) r s (finGL E r k, 1) = finGL E (r + s) (lev (Af E) r s (k, 1)) := by
    rw [← lev_finGL, map_one]
  have hY : finGL E (r + s) (lev (Af E) r s (k, 1)) * finGL E (r + s) t =
      finGL E (r + s) t * finGL E (r + s) (t⁻¹ * lev (Af E) r s (k, 1) * t) := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  rw [lev_mul_one, e1, mul_assoc (lev (Ad E) r s (m, m₂)), hY, mul_assoc _ (infGL E (r + s) c), infGL_comm]
  simp only [mul_assoc]

end GlobalTheory.CompanionTheory.CTFin.Slice1
end

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem commute_rt_of_mem_Zalg {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (h : GA E a) :
    Commute z (rt E a h) := by
  have hc : ∀ τ u, Commute (cap (a := a) τ u) (rt E a h) := fun τ u => by
    rw [← infGL_mul_finGL h, map_mul]
    exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _).mul_right (commute_cap_finRep τ u _)
  induction hz using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨τ, u, rfl⟩ := hx; exact hc τ u
  | algebraMap c => exact Algebra.commute_algebraMap_left c _
  | add x y _ _ hx hy => exact hx.add_left hy
  | mul x y _ _ hx hy => exact hx.mul_left hy

theorem zfin_of_cofin {J : Set (Module.End ℂ (Sm E a))} (hJ : Cofin J) {φ : Sm E a} (h : ∀ z ∈ J, z φ = 0) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) := by
  obtain ⟨-, V, hV, hz⟩ := hJ
  let ev : Module.End ℂ (Sm E a) →ₗ[ℂ] Sm E a := LinearMap.applyₗ φ
  have hev : ∀ z, ev z = z φ := fun _ => rfl
  have hw0 : ∀ w ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E a, ∃ j ∈ J, y = x * j}, ev w = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, -, j, hj, rfl⟩ := hy
        rw [hev, Module.End.mul_apply, h j hj, map_zero]
      | zero => exact map_zero ev
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul c x _ hx => rw [map_smul, hx, smul_zero]
  have hle : Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) ≤ V.map ev := by
    rw [Submodule.span_le]
    rintro _ ⟨z, hz', rfl⟩
    obtain ⟨v, hv, w, hw, hvw⟩ := Submodule.mem_sup.1 (hz z hz')
    refine ⟨v, hv, ?_⟩
    change ev v = ev z
    rw [← hvw, map_add, hw0 w hw, add_zero]
  haveI := hV
  exact Submodule.finiteDimensional_of_le hle

theorem fd_span_of_forall_mem {K X : Type} (C : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ C] (f : K → X → ℂ)
    (hf : ∀ x, (fun k => f k x) ∈ C) : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) := by
  let b := Module.finBasis ℂ C
  let A : Fin (Module.finrank ℂ C) → X → ℂ := fun i x => b.repr ⟨_, hf x⟩ i
  have hA : ∀ k, f k = ∑ i, (b i : K → ℂ) k • A i := by
    intro k
    funext x
    have e := congrArg (fun c : C => (c : K → ℂ) k) (b.sum_repr ⟨_, hf x⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, A]
    rw [← e]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hle : Submodule.span ℂ (Set.range f) ≤ Submodule.span ℂ (Set.range A) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [hA k]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range A)) := FiniteDimensional.span_of_finite ℂ (Set.finite_range A)
  exact Submodule.finiteDimensional_of_le hle

theorem kfin_of_coeff {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W)
    (φ : Sm E a) (h : ∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) := by
  haveI := GlobalTheory.CompanionTheory.CTFin.UniSol.finiteDimensional_coeffSpan ρ
  haveI := fd_span_of_forall_mem _ (fun k => (cptRep E a k φ).1) h
  let S := Submodule.span ℂ (Set.range fun k => cptRep E a k φ)
  have e : S.map (Sm E a).subtype = Submodule.span ℂ (Set.range fun k => (cptRep E a k φ).1) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  haveI : FiniteDimensional ℂ (S.map (Sm E a).subtype) := by rw [e]; infer_instance
  exact (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) S).symm.finiteDimensional

theorem coeff_comp {K K' W : Type} [Group K] [Group K'] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K' W)
    (f : K →* K') (κ : K') {c : K' → ℂ} (hc : c ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) :
    (fun k => c (f k * κ)) ∈ GlobalTheory.Published.AutFin.coeffSpan (ρ.comp f) := by
  let T : (K' → ℂ) →ₗ[ℂ] (K → ℂ) := LinearMap.funLeft ℂ ℂ (fun k => f k * κ)
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ (GlobalTheory.Published.AutFin.coeffSpan (ρ.comp f)).comap T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨ℓ, w, rfl⟩
    refine Submodule.subset_span ⟨ℓ, ρ κ w, funext fun k => ?_⟩
    simp [T, LinearMap.funLeft, map_mul, Module.End.mul_apply]
  exact hle hc

end GlobalTheory.CompanionTheory.CTFin.Slice1
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatApplyEquiv
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegCoarse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) : Fin s → Segment k := fun a =>
  Segment.ofFirst (Δ.first.nu ((∑ b ∈ Finset.univ.filter (fun b => a < b), c b : ℕ) : ℂ)) (Δ.isCusp_first.nu _)
    (c a) (hc a)

@[simp] theorem len_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (a : Fin s) :
    (topCut Δ c hc a).len = c a := rfl

theorem isTopCut_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (h : ∑ a, c a = Δ.len) :
    IsTopCut Δ (topCut Δ c hc) :=
  ⟨h, fun _ => rfl⟩

theorem eq_topCut {Δ : Segment k} {s : ℕ} {Γ : Fin s → Segment k} (h : IsTopCut Δ Γ) :
    Γ = topCut Δ (fun a => (Γ a).len) (fun a => (Γ a).len_pos) :=
  funext fun a => Segment.ext_first (by rw [h.2 a]; rfl) rfl

theorem sum_split {s : ℕ} (c : Fin s → ℕ) (a : Fin s) :
    ∑ b, c b = (∑ t : Fin a, c (Fin.castLE a.2.le t)) + c a + ∑ b ∈ Finset.univ.filter (fun b => a < b), c b := by
  have h1 : ∑ t : Fin a, c (Fin.castLE a.2.le t) = ∑ b ∈ Finset.univ.filter (fun b : Fin s => b < a), c b := by
    refine Finset.sum_bij (fun t _ => Fin.castLE a.2.le t)
      (fun t _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.lt_def.2 t.2⟩)
      (fun t _ u _ h => Fin.castLE_injective _ h) (fun b hb => ?_) (fun _ _ => rfl)
    have hb' : (b : ℕ) < a := Fin.lt_def.1 (Finset.mem_filter.1 hb).2
    exact ⟨⟨b, hb'⟩, Finset.mem_univ _, rfl⟩
  rw [h1]
  have h2 : ∑ b, c b = ∑ b, ((if b < a then c b else 0) + (if b = a then c b else 0) + (if a < b then c b else 0)) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases lt_trichotomy b a with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  rw [h2, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
    ← Finset.sum_filter, Finset.filter_eq', if_pos (Finset.mem_univ _), Finset.sum_singleton]

theorem concat_dec_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (h : ∑ a, c a = Δ.len)
    (i : Fin (∑ a, c a)) : concat c (fun a => dec (topCut Δ c hc a)) i = dec Δ (Fin.cast h i) := by
  show dec (topCut Δ c hc (finSigmaFinEquiv.symm i).1) (finSigmaFinEquiv.symm i).2 = dec Δ (Fin.cast h i)
  rcases hq : finSigmaFinEquiv.symm i with ⟨a, j⟩
  have hi : (i : ℕ) = (∑ t : Fin a, c (Fin.castLE a.2.le t)) + j := by
    rw [← Equiv.apply_symm_apply finSigmaFinEquiv i, hq, finSigmaFinEquiv_apply]
  have hs := sum_split c a
  have hj : (j : ℕ) < c a := j.2
  simp only [dec, Segment.term, topCut, Segment.first_ofFirst, IrrGL.nu_nu]
  congr 1
  simp only [Fin.val_rev, Fin.val_cast, Segment.len_ofFirst]
  have key : Δ.len - (i + 1) = (∑ b ∈ Finset.univ.filter (fun b => a < b), c b) + (c a - (j + 1)) := by
    rw [← h]; omega
  rw [key]
  push_cast
  ring

theorem concat_injective {s : ℕ} {c : Fin s → ℕ} {x x' : ∀ a, Fin (c a) → IrrGL k} (h : concat c x = concat c x') :
    x = x' := by
  funext a j
  have := congrFun h (finSigmaFinEquiv ⟨a, j⟩)
  change (fun p : (b : Fin s) × Fin (c b) => x p.1 p.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨a, j⟩)) =
    (fun p : (b : Fin s) × Fin (c b) => x' p.1 p.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨a, j⟩)) at this
  rw [Equiv.symm_apply_apply] at this
  exact this

theorem concat_apply_equiv {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL k) (p : (a : Fin s) × Fin (c a)) :
    concat c x (finSigmaFinEquiv p) = x p.1 p.2 := by
  change (fun q : (b : Fin s) × Fin (c b) => x q.1 q.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv p)) = _
  rw [Equiv.symm_apply_apply]

theorem sum_concat {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL k) :
    ∑ i, (concat c x i).1 = ∑ a, ∑ j, (x a j).1 := by
  rw [← Equiv.sum_comp finSigmaFinEquiv, Fintype.sum_sigma]
  simp only [concat_apply_equiv]

theorem sum_dec (Δ : Segment k) : ∑ a, (dec Δ a).1 = Δ.deg := by
  rw [← Segment.sum_term_fst]
  exact Equiv.sum_comp Fin.revPerm (fun a => (Δ.term a).1)

theorem deg_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (a : Fin s) :
    (topCut Δ c hc a).deg = c a * Δ.d := rfl

theorem jm_reindex {n m N : ℕ} (h : n = m) (x : Fin n → IrrGL k) (x' : Fin m → IrrGL k)
    (hx : ∀ i, x i = x' (Fin.cast h i)) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x' a).1 = N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : jm x hd π = jm x' hd' π := by
  subst h
  obtain rfl : x = x' := funext fun i => by simpa using hx i
  rfl

theorem eq_of_isLSeg {Γ : Segment k} {x x' : IrrGL k} (h : IsLSeg Γ x.rep) (h' : IsLSeg Γ x'.rep) : x = x' := by
  obtain ⟨n, c⟩ := x
  obtain ⟨n', c'⟩ := x'
  have e1 := h.deg_eq
  have e2 := h'.deg_eq
  obtain rfl : n = n' := e1.symm.trans e2
  obtain ⟨φ⟩ := h.unique h'
  have := (IrrGL.of_eq_of (π := IrrGL.rep (k := k) ⟨n, c'⟩) (σ := IrrGL.rep (k := k) ⟨n, c⟩)
    (hs := c'.rep.smooth) (hi := c'.rep.irr) (hs' := c.rep.smooth) (hi' := c.rep.irr)).2 ⟨φ⟩
  rw [IrrGL.of_rep, IrrGL.of_rep] at this
  exact this.symm

end GlobalTheory.CompanionTheory.SegCoarse

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeasureLocallyFinite
section
noncomputable section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise

open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ConeHaar.Fin

variable {n : ℕ}

theorem continuous_hOf : Continuous (hOf (n := n)) := by
  unfold hOf
  refine continuous_finset_sum _ fun p _ => ?_
  exact (Complex.continuous_ofReal.comp (continuous_apply p)).smul continuous_const

theorem continuous_detRe : Continuous fun v : Fin n × Fin n → ℝ => (hOf v).det.re :=
  Complex.continuous_re.comp (continuous_hOf.matrix_det)

theorem detRe_pos {v : Fin n × Fin n → ℝ} (hv : v ∈ cone n) : 0 < (hOf v).det.re := by
  have h : 0 < (hOf v).det := Matrix.PosDef.det_pos hv
  exact (Complex.pos_iff.1 h).1

theorem measurable_coneW : Measurable (coneW n) := by
  unfold coneW
  exact ENNReal.measurable_ofReal.comp ((continuous_detRe.measurable.pow_const n).inv)

theorem exists_hOf_eq_one : ∃ v : Fin n × Fin n → ℝ, hOf v = 1 := by
  refine ⟨fun p => ((1 * hb p : Mat n).trace).re, ?_⟩
  have hre : ∀ p : Fin n × Fin n, ((((1 * hb p : Mat n).trace).re : ℝ) : ℂ) = (1 * hb p : Mat n).trace := by
    intro p
    apply Complex.conj_eq_iff_re.1
    have h1 : star (hb p : Mat n).trace = (hb p : Mat n).trace := by
      rw [← Matrix.trace_conjTranspose, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose]
    simpa using h1
  have h := (GlobalTheory.CompanionTheory.TopClass.hbB n).sum_repr (1 : Mat n)
  simp only [GlobalTheory.CompanionTheory.TopClass.hbB_repr, GlobalTheory.CompanionTheory.TopClass.hbB_apply] at h
  conv_rhs => rw [← h]
  simp only [hOf, hre]

theorem cone_nonempty : (cone n).Nonempty := by
  obtain ⟨v, hv⟩ := exists_hOf_eq_one (n := n)
  refine ⟨v, ?_⟩
  show (hOf v).PosDef
  rw [hv]
  exact Matrix.PosDef.one

theorem coneW_pos {v : Fin n × Fin n → ℝ} (hv : v ∈ cone n) : coneW n v ≠ 0 := by
  unfold coneW
  have : 0 < ((hOf v).det.re ^ n)⁻¹ := inv_pos.2 (pow_pos (detRe_pos hv) n)
  exact (ENNReal.ofReal_pos.2 this).ne'

theorem coneMeas_ne_zero : coneMeas n ≠ 0 := by
  intro h0
  have hz := (withDensity_eq_zero measurable_coneW.aemeasurable h0)
  have hopen : IsOpen (cone n) := GlobalTheory.T.positive_cone_isOpen n
  have hvol : 0 < volume (cone n) := hopen.measure_pos volume cone_nonempty
  rw [Filter.EventuallyEq, ae_restrict_iff' hopen.measurableSet] at hz
  have hnull : volume (cone n) = 0 := by
    refine measure_mono_null (t := {v | ¬ (v ∈ cone n → coneW n v = (0 : (Fin n × Fin n → ℝ) → ℝ≥0∞) v)}) ?_ hz
    intro v hv
    simpa using ⟨hv, coneW_pos hv⟩
  exact hvol.ne' hnull

theorem coneMeas_lt_top (C : Set (Fin n × Fin n → ℝ)) (hC : IsCompact C) (hCc : C ⊆ cone n) :
    coneMeas n C < ⊤ := by
  have hcont : ContinuousOn (fun v : Fin n × Fin n → ℝ => ((hOf v).det.re ^ n)⁻¹) C :=
    ContinuousOn.inv₀ (continuous_detRe.pow n).continuousOn
      fun v hv => (pow_pos (detRe_pos (hCc hv)) n).ne'
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hcont
  have hle : ∀ v ∈ C, coneW n v ≤ ENNReal.ofReal M := fun v hv =>
    ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hM v hv))
  unfold coneMeas
  rw [withDensity_apply _ hC.measurableSet]
  calc ∫⁻ v in C, coneW n v ∂(volume.restrict (cone n))
      ≤ ∫⁻ _ in C, ENNReal.ofReal M ∂(volume.restrict (cone n)) :=
        setLIntegral_mono' hC.measurableSet hle
    _ = ENNReal.ofReal M * (volume.restrict (cone n)) C := by simp
    _ ≤ ENNReal.ofReal M * volume C := by
        gcongr
        exact Measure.restrict_le_self
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.measure_lt_top

theorem coneMeas_ne_zero_and_lt_top : ∀ n : ℕ, coneMeas n ≠ 0 ∧ ∀ C : Set (Fin n × Fin n → ℝ), IsCompact C →
    C ⊆ PositivityTheory.RgBcC.cone n → coneMeas n C < ⊤ :=
  fun _ => ⟨coneMeas_ne_zero, coneMeas_lt_top⟩

end GlobalTheory.CompanionTheory.ConeHaar.Fin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleSurjectionFactor
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.Segments

theorem exists_coatom_ge_of_hasFiniteLength {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {P : Representation ℂ G V} (hfl : HasFiniteLength P) (S : Subrepresentation P) (hS : S ≠ ⊤) :
    ∃ C : Subrepresentation P, IsCoatom C ∧ S ≤ C := by
  obtain ⟨hN, -⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hfl
  have : IsCoatomic (Submodule (MonoidAlgebra ℂ G) P.asModule) := inferInstance
  have hc : IsCoatomic (Subrepresentation P) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := P)).isCoatomic_iff.2 this
  obtain h | ⟨C, hC, hle⟩ := hc.eq_top_or_exists_le_coatom S
  · exact absurd h hS
  · exact ⟨C, hC, hle⟩

theorem cosocle_quotient_of_quotient : ∀ {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (P : Representation ℂ G V)
    (Q : Representation ℂ G X) (hc : IsCosocle σ P) (hfl : HasFiniteLength P) (f : P.IntertwiningMap Q)
    (hf : Function.Surjective f) (hQ : Nontrivial X), ∃ g : Q.IntertwiningMap σ, Function.Surjective g := by
  intro G V W X _ _ _ _ _ _ _ σ P Q hc hfl f hf hQ
  obtain ⟨-, f0, hf0, hco⟩ := hc
  have hne : Representation.IntertwiningMap.ker P Q f ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    obtain ⟨v, rfl⟩ := hf x
    have hv : v ∈ (⊤ : Subrepresentation P) := trivial
    rw [← h] at hv
    exact hx hv
  obtain ⟨C, hC, hle⟩ := exists_coatom_ge_of_hasFiniteLength hfl _ hne
  have hk : ∀ v : V, f v = 0 → f0 v = 0 := by
    intro v hv
    have h1 : v ∈ Representation.IntertwiningMap.ker P Q f := hv
    have h2 : v ∈ C := hle h1
    rw [hco C hC] at h2
    exact h2
  let e := LinearMap.quotKerEquivOfSurjective f.toLinearMap hf
  let gl : X →ₗ[ℂ] W :=
    (LinearMap.ker f.toLinearMap).liftQ f0.toLinearMap (fun v hv => hk v hv) ∘ₗ e.symm.toLinearMap
  have hgl : ∀ v : V, gl (f v) = f0 v := by
    intro v
    have h1 : e.symm (f v) = Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [gl, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, Submodule.liftQ_apply]
    rfl
  refine ⟨⟨gl, fun h => ?_⟩, ?_⟩
  · refine LinearMap.ext fun x => ?_
    obtain ⟨v, rfl⟩ := hf x
    have h2 : Q h (f v) = f (P h v) := by
      have := congrArg (fun m => m v) (f.isIntertwining' h)
      exact this.symm
    have h3 : f0 (P h v) = σ h (f0 v) := congrArg (fun m => m v) (f0.isIntertwining' h)
    simp only [LinearMap.comp_apply]
    rw [h2, hgl, hgl, h3]
  · intro w
    obtain ⟨v, rfl⟩ := hf0 w
    exact ⟨f v, hgl v⟩

end GlobalTheory.CompanionTheory.Segments
end

