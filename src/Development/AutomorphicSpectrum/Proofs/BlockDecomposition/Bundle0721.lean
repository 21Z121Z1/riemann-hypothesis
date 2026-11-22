import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleOfLinearReductive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0698
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0432
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0184
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0012
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0063
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0584
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0511
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0412

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryKTypeFinite
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.AdmGL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}

open scoped Classical in

def toGL (M : Matrix (Fin a) (Fin a) (ι → ℂ)) : GL (Fin a) (ι → ℂ) :=
  if h : IsUnit M then h.unit else 1

theorem coe_toGL {M : Matrix (Fin a) (Fin a) (ι → ℂ)} (h : IsUnit M) : (toGL M : Matrix (Fin a) (Fin a) (ι → ℂ)) = M := by
  simp [toGL, h]

theorem toGL_coe (u : GL (Fin a) (ι → ℂ)) : toGL (u : Matrix (Fin a) (Fin a) (ι → ℂ)) = u :=
  Units.ext (coe_toGL u.isUnit)

def blkRep {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : Fin a × ι ≃ Fin n)
    (σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) : H →L[ℂ] H :=
  σ (toGL (unblk e g))

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem blkRep_blk (e : Fin a × ι ≃ Fin n) (σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)) (u : GL (Fin a) (ι → ℂ)) :
    blkRep e σ (blk e (u : Matrix (Fin a) (Fin a) (ι → ℂ))) = σ u := by
  rw [blkRep, unblk_blk, toGL_coe]

theorem blk_coe_mem (e : Fin a × ι ≃ Fin n) (u : GL (Fin a) (ι → ℂ)) :
    blk e (u : Matrix (Fin a) (Fin a) (ι → ℂ)) ∈ blkG e := ⟨_, u.isUnit, rfl⟩

theorem exists_gl_of_mem (e : Fin a × ι ≃ Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ blkG e) :
    ∃ u : GL (Fin a) (ι → ℂ), g = blk e (u : Matrix (Fin a) (Fin a) (ι → ℂ)) := by
  obtain ⟨M, hM, rfl⟩ := hg
  exact ⟨hM.unit, rfl⟩

theorem continuousOn_toGL_unblk (e : Fin a × ι ≃ Fin n) :
    ContinuousOn (fun g => toGL (unblk e g) : Matrix (Fin n) (Fin n) ℂ → GL (Fin a) (ι → ℂ)) (blkG e) := by
  rw [continuousOn_iff_continuous_restrict]
  have hval : ∀ g : blkG e, ((toGL (unblk e g.1) : GL (Fin a) (ι → ℂ)) : Matrix (Fin a) (Fin a) (ι → ℂ)) = unblk e g.1 := by
    rintro ⟨_, M, hM, rfl⟩
    rw [unblk_blk]
    exact coe_toGL hM
  have hinv : ∀ g : blkG e, (((toGL (unblk e g.1))⁻¹ : GL (Fin a) (ι → ℂ)) : Matrix (Fin a) (Fin a) (ι → ℂ)) =
      unblk e (g.1.det⁻¹ • g.1.adjugate) := by
    rintro ⟨_, M, hM, rfl⟩
    have h := blk_inv e hM
    rw [Matrix.inv_def, Ring.inverse_eq_inv'] at h
    simp only [h, unblk_blk]
    rw [Matrix.coe_units_inv, coe_toGL hM]
  have hdet : ∀ g : blkG e, g.1.det ≠ 0 := fun g =>
    ((Matrix.isUnit_iff_isUnit_det _).1 ((mem_blkG_iff e).1 g.2).1).ne_zero
  have hc : Continuous fun g : blkG e => g.1.det⁻¹ • g.1.adjugate :=
    (Continuous.inv₀ continuous_subtype_val.matrix_det hdet).smul continuous_subtype_val.matrix_adjugate
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact ((continuous_unblk e).comp continuous_subtype_val).congr fun g => (hval g).symm
  · exact ((continuous_unblk e).comp hc).congr fun g => (hinv g).symm

theorem isURepOn_blkRep (e : Fin a × ι ≃ Fin n) {σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)} (hσ : IsUnitaryRep σ) :
    Formalism.MainNotions.S.IsURepOn (blkG e) (blkRep e σ) := by
  refine ⟨⟨?_, ?_⟩, fun g _ v => hσ.norm_apply _ v, fun v =>
    (hσ.continuous_apply v).comp_continuousOn (continuousOn_toGL_unblk e)⟩
  · have h := blkRep_blk e σ 1
    simpa using h
  · intro g hg h hh
    obtain ⟨u, rfl⟩ := exists_gl_of_mem e hg
    obtain ⟨v, rfl⟩ := exists_gl_of_mem e hh
    rw [← blk_mul, ← Units.val_mul, blkRep_blk, blkRep_blk, blkRep_blk, map_mul]
    rfl

theorem isIrredOn_blkRep (e : Fin a × ι ≃ Fin n) {σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)}
    (hi : IsTopIrreducible σ) : Formalism.MainNotions.S.IsIrredOn (blkG e) (blkRep e σ) := fun S hS hinv =>
  hi.2 S ⟨hS, fun u v hv => by
    have h := hinv _ (blk_coe_mem e u) v hv
    rwa [blkRep_blk] at h⟩

theorem blk_mem_maxCpt (e : Fin a × ι ≃ Fin n) (k : Matrix.unitaryGroup (Fin a) (ι → ℂ)) :
    blk e k.1 ∈ GlobalTheory.LinRed.maxCpt (blkG e) := by
  refine ⟨blk_coe_mem e (Unitary.toUnits k), ?_⟩
  rw [SetLike.mem_coe, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← blk_conjTranspose, ← blk_mul,
    ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff).1 k.2, blk_one]

theorem exists_unitary_of_mem_maxCpt (e : Fin a × ι ≃ Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ GlobalTheory.LinRed.maxCpt (blkG e)) :
    ∃ k : Matrix.unitaryGroup (Fin a) (ι → ℂ), g = blk e k.1 := by
  obtain ⟨⟨M, -, rfl⟩, hu⟩ := hg
  refine ⟨⟨M, ?_⟩, rfl⟩
  rw [SetLike.mem_coe, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← blk_conjTranspose, ← blk_mul,
    ← blk_one e, ← Matrix.star_eq_conjTranspose] at hu
  rw [Matrix.mem_unitaryGroup_iff]
  exact blk_injective e hu

theorem finiteDimensional_isoPart_gl [CompleteSpace H] {σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)}
    (hσ : IsUnitaryRep σ) (hi : IsTopIrreducible σ) {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin a) (ι → ℂ)) W) :
    FiniteDimensional ℂ (isoPart (σ.comp Unitary.toUnits) ρ) := by
  let e := Fintype.equivFin (Fin a × ι)
  have hLR := isLinRed_blkG e
  have hA := GlobalTheory.CompanionTheory.admitted.isAdmissible_of_unitary_irreducible hLR
    (GlobalTheory.CompanionTheory.AdmIwa.RamifiedPrimeLengthBound hLR (GlobalTheory.CompanionTheory.IwaGen.iwaOn_of_isLinRed hLR)) H (blkRep e σ)
    (isURepOn_blkRep e hσ) (isIrredOn_blkRep e hi)
  have hrep : ∀ k : Matrix.unitaryGroup (Fin a) (ι → ℂ),
      blkRep e σ (blk e k.1) = (σ.comp Unitary.toUnits) k := fun k => blkRep_blk e σ (Unitary.toUnits k)
  refine finiteDimensional_isoPart (π := σ.comp Unitary.toUnits) (fun k v => hσ.norm_apply _ v) ?_ _ W ρ rfl
  intro S hfd hS hirr
  have hKS : GlobalTheory.LinRed.IsKStable (blkG e) (blkRep e σ) S := by
    intro g hg w hw
    obtain ⟨k, rfl⟩ := exists_unitary_of_mem_maxCpt e hg
    rw [hrep]
    exact hS k w hw
  have hirr' : ∀ S' : Submodule ℂ H, S' ≤ S → GlobalTheory.LinRed.IsKStable (blkG e) (blkRep e σ) S' → S' = ⊥ ∨ S' = S :=
    fun S' hle hst => hirr S' hle fun k w hw => by
      have h := hst _ (blk_mem_maxCpt e k) w hw
      rwa [hrep] at h
  have hfin := hA.2.2.2 S hfd hKS hirr'
  have heq : {S' : Submodule ℂ H | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧
      ∀ k, ∀ w ∈ S, T ((σ.comp Unitary.toUnits) k w) = (σ.comp Unitary.toUnits) k (T w)} =
      {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧ ∀ k ∈ GlobalTheory.LinRed.maxCpt (blkG e), ∀ w ∈ S,
        T (blkRep e σ k w) = blkRep e σ k (T w)} := by
    ext S'
    constructor
    · rintro ⟨T, rfl, hT⟩
      refine ⟨T, rfl, fun g hg w hw => ?_⟩
      obtain ⟨k, rfl⟩ := exists_unitary_of_mem_maxCpt e hg
      rw [hrep]
      exact hT k w hw
    · rintro ⟨T, rfl, hT⟩
      refine ⟨T, rfl, fun k w hw => ?_⟩
      rw [← hrep]
      exact hT _ (blk_mem_maxCpt e k) w hw
  rw [heq]
  exact hfin

theorem admissible_GL_Cinf : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : GL (Fin a) (Cinf E) →* (H →L[ℂ] H)), IsUnitaryRep σ → IsTopIrreducible σ → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W), FiniteDimensional ℂ ↥(⨆ (T : W →ₗ[ℂ] H) (_ : ∀ k w, T (ρ k w) = σ (Unitary.toUnits k) (T w)), LinearMap.range T : Submodule ℂ H) := by
  intro E _ _ _ a H _ _ _ σ hσ hi W _ _ _ ρ
  classical
  exact finiteDimensional_isoPart_gl hσ hi ρ

end GlobalTheory.CompanionTheory.AdmGL

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursProductInterleave
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.WordProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem row_ne_zero {n p N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsSmooth π) (zz : Fin n → IrrGL k) (σ : Fin p ↪o Fin n)
    (c : Fin n → ℕ) (hc : ∀ a, c (σ a) = (zz (σ a)).1) (hc0 : ∀ j, j ∉ Set.range σ → c j = 0)
    (hz : ∑ a, (zz (σ a)).1 = N) (f : (Σ j, Fin (c j)) ≃ Fin N) (h : jm (fun a => zz (σ a)) hz π ≠ 0) :
    jhMult (piTensor fun j => (clOf (zz j) (c j)).rep.ρ) (jac f π) ≠ 0 :=
  GlobalTheory.T.jacquet_multiplicity_order_embedding π hπ zz σ c hc hc0 hz f h

theorem col_equiv (a : IrrGL k) {α : Type} [Fintype α] [LinearOrder α] (b : α → ℕ) (i₀ : α)
    (hb : b i₀ = a.1) (hb0 : ∀ i, i ≠ i₀ → b i = 0) (g : (Σ i, Fin (b i)) ≃ Fin a.1) :
    Nonempty ((multiProd g fun i => (clOf a (b i)).rep.ρ).Equiv a.rep) :=
  GlobalTheory.T.multi_product_single_factor_equiv a b i₀ hb hb0 g

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem interleave_embed {T : Type 1} {u v w : List T} (h : Zc.Comb.Interleave u v w) :
    ∃ (r : Fin w.length → Fin 2) (σ₀ : Fin u.length ↪o Fin w.length) (σ₁ : Fin v.length ↪o Fin w.length),
      (∀ j, r j = 0 ↔ j ∈ Set.range σ₀) ∧ (∀ j, r j = 1 ↔ j ∈ Set.range σ₁) ∧
        (∀ a, w.get (σ₀ a) = u.get a) ∧ (∀ a, w.get (σ₁ a) = v.get a) :=
  GlobalTheory.T.interleaving_two_colour_embedding h

theorem jm_congr' {h N : ℕ} {x x' : Fin h → IrrGL k} (e : x = x') (hd : ∑ a, (x a).1 = N)
    (hd' : ∑ a, (x' a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) :
    jm x hd π = jm x' hd' π := by
  subst e; rfl

theorem sum_ite_range {n p : ℕ} (σ : Fin p ↪o Fin n) (P : Fin n → Prop) [DecidablePred P]
    (hP : ∀ j, P j ↔ j ∈ Set.range σ) (F : Fin n → ℕ) :
    ∑ j, (if P j then F j else 0) = ∑ a, F (σ a) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun a _ => σ a) (fun a _ => by simp [hP]) (fun a _ b _ h => σ.injective h)
    (fun j hj => ?_) (fun a _ => rfl)
  obtain ⟨a, rfl⟩ := (hP j).1 (Finset.mem_filter.1 hj).2
  exact ⟨a, Finset.mem_univ _, rfl⟩

theorem jhMult_jac_multiProd_ne_zero {α β n : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    [Fintype n] [DecidableEq n] {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
    (E : (Σ i, m i) ≃ n) (E' : (Σ j, m' j) ≃ n)
    {X : α → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)) (hs : ∀ i, IsSmooth (ρ i))
    (hl : ∀ i, HasFiniteLength (ρ i)) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (Levi k m') Y) (hτ : τ.IsIrreducible) (hτs : IsSmooth τ)
    (b₀ : SizeMatrix m m') (s₀ : ∀ i j, IrrCl (GL (Fin (b₀.1 i j)) k))
    (hrow : ∀ (f : ∀ i, (Σ j, Fin (b₀.1 i j)) ≃ m i) i,
      jhMult (piTensor fun j => (s₀ i j).rep.ρ) (jac (f i) (ρ i)) ≠ 0)
    (hcol : ∀ g : ∀ j, (Σ i, Fin (b₀.1 i j)) ≃ m' j,
      jhMult τ (piTensor fun j => multiProd (g j) fun i => (s₀ i j).rep.ρ) ≠ 0) :
    jhMult τ (jac E' (multiProd E ρ)) ≠ 0 := by
  classical
  haveI : Fintype (SizeMatrix m m') := Fintype.ofFinite _
  have hG := GlobalTheory.CompanionTheory.GeoLink.geometricLemma k
  let f : ∀ (b : SizeMatrix m m') i, (Σ j, Fin (b.1 i j)) ≃ m i := fun b => b.nonempty_rows.some
  let g : ∀ (b : SizeMatrix m m') j, (Σ i, Fin (b.1 i j)) ≃ m' j := fun b => b.nonempty_cols.some
  rw [multiProd, hG.1.jhMult_eq E E' (isSmooth_piTensor hs) f g hτ]
  intro h0
  refine absurd ((Finset.sum_eq_zero_iff.1 h0) b₀ (Finset.mem_univ _)) ?_
  obtain ⟨T, hTout, hT⟩ := hG.2 α β m m' (fun i j => Fin (b₀.1 i j)) (f b₀) (g b₀) X ρ hs hl
  rw [show jhMult τ (cellFunctor (f b₀) (g b₀) (piTensor ρ)) = _ from hT ⟨Y, τ, hτs, hτ⟩]
  have hmem : s₀ ∈ T := by
    by_contra hn
    obtain ⟨i, hi⟩ := hTout s₀ hn
    exact hrow (f b₀) i hi
  intro hsum
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => hrow (f b₀) i) (hcol (g b₀))
    ((Finset.sum_eq_zero_iff.1 hsum) s₀ hmem)

theorem wd_prod₂_of_interleave_fin (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (X : Fin 2 → IrrGL k)
    (u v w : List (IrrGL k)) (hxu : Wd (X 0).rep u) (hyv : Wd (X 1).rep v) (hw : Zc.Comb.Interleave u v w) :
    Wd (prod₂ (X 0).rep (X 1).rep) w := by
  classical
  obtain ⟨hdu, hju⟩ := hxu
  obtain ⟨hdv, hjv⟩ := hyv
  have hE := interleave_embed (T := IrrGL k) hw
  obtain ⟨r, σ₀, σ₁, hE⟩ := hE
  obtain ⟨hr0, hr1, hw0, hw1⟩ := hE
  let n := w.length
  let m : Fin 2 → Type := fun i => Fin (X i).1
  let m' : Fin n → Type := fun j => Fin (w.get j).1
  have hdeg0 : ∑ a, (w.get (σ₀ a)).1 = (X 0).1 := by
    rw [← hdu]; exact Finset.sum_congr rfl fun a _ => by rw [hw0]
  have hdeg1 : ∑ a, (w.get (σ₁ a)).1 = (X 1).1 := by
    rw [← hdv]; exact Finset.sum_congr rfl fun a _ => by rw [hw1]
  have hrow : ∀ i : Fin 2, ∑ j, (if r j = i then (w.get j).1 else 0) = (X i).1 := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · exact (sum_ite_range σ₀ _ hr0 _).trans hdeg0
    · exact (sum_ite_range σ₁ _ hr1 _).trans hdeg1
  have hsplit : ∀ j, (w.get j).1 =
      (if r j = 0 then (w.get j).1 else 0) + (if r j = 1 then (w.get j).1 else 0) := by
    intro j
    rcases Fin.exists_fin_two.1 ⟨r j, rfl⟩ with h | h <;> simp [h]
  have hd' : ∑ j, (w.get j).1 = (X 0).1 + (X 1).1 := by
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) (hrow 0) (hrow 1)
  have hd : ∑ a, (X a).1 = (X 0).1 + (X 1).1 := Fin.sum_univ_two _
  let b₀ : SizeMatrix m m' := ⟨fun i j => if r j = i then (w.get j).1 else 0, fun i => by
    simpa [m] using hrow i, fun j => by
    rcases Fin.exists_fin_two.1 ⟨r j, rfl⟩ with h | h <;> simp [m', h]⟩
  let ρ : ∀ i, Representation ℂ (GL (m i) k) (X i).2.rep.V := fun i => (X i).rep
  have hs : ∀ i, IsSmooth (ρ i) := fun i => (X i).2.rep.smooth
  have hl : ∀ i, HasFiniteLength (ρ i) := fun i => hasFiniteLength_of_isIrreducible (X i).2.rep.irr
  let τ := piTensor fun j : Fin n => (w.get j).rep
  have hτ : τ.IsIrreducible := GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA w.get
  have hτs : IsSmooth τ := isSmooth_piTensor fun j => (w.get j).2.rep.smooth
  let s₀ : ∀ i j, IrrCl (GL (Fin (b₀.1 i j)) k) := fun i j => clOf (w.get j) (b₀.1 i j)
  have hrowf : ∀ (f : ∀ i, (Σ j, Fin (b₀.1 i j)) ≃ m i) i,
      jhMult (piTensor fun j => (s₀ i j).rep.ρ) (jac (f i) (ρ i)) ≠ 0 := by
    intro f
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · refine row_ne_zero (X 0).rep (hs 0) w.get σ₀ (fun j => b₀.1 0 j) (fun a => ?_) (fun j hj => ?_) hdeg0
        (f 0) ?_
      · simp [b₀, (hr0 (σ₀ a)).2 ⟨a, rfl⟩]
      · simp [b₀, mt (hr0 j).1 hj]
      · rw [jm_congr' (funext hw0) hdeg0 hdu]; exact hju
    · refine row_ne_zero (X 1).rep (hs 1) w.get σ₁ (fun j => b₀.1 1 j) (fun a => ?_) (fun j hj => ?_) hdeg1
        (f 1) ?_
      · simp [b₀, (hr1 (σ₁ a)).2 ⟨a, rfl⟩]
      · simp [b₀, mt (hr1 j).1 hj]
      · rw [jm_congr' (funext hw1) hdeg1 hdv]; exact hjv
  have hcolf : ∀ g : ∀ j, (Σ i, Fin (b₀.1 i j)) ≃ m' j,
      jhMult τ (piTensor fun j => multiProd (g j) fun i => (s₀ i j).rep.ρ) ≠ 0 := by
    intro g
    have hcol : ∀ j, Nonempty ((multiProd (g j) fun i => (s₀ i j).rep.ρ).Equiv (w.get j).rep) := fun j =>
      col_equiv (w.get j) (fun i => b₀.1 i j) (r j) (by simp [b₀]) (fun i hi => by simp [b₀, Ne.symm hi])
        (g j)
    rw [jhMult_congr_right τ (piTensorEquiv fun j => (hcol j).some), jhMult_self hτ]
    exact one_ne_zero
  refine ⟨hd', ?_⟩
  have hφ : Nonempty ((prod₂ (X 0).rep (X 1).rep).Equiv (prodIrr X hd)) :=
    nonempty_prod₂_equiv_prodIrr_rep X hd
  let E' := stdBlocks (fun a => (w.get a).1) hd'
  have e1 : jm w.get hd' (prod₂ (X 0).rep (X 1).rep) = jhMult τ (jac E' (prodIrr X hd)) :=
    jhMult_congr_right τ (GlobalTheory.SmGL.Exponents.jacEquiv E' hφ.some)
  rw [e1]
  exact jhMult_jac_multiProd_ne_zero (stdBlocks (fun a => (X a).1) hd) E' ρ hs hl τ hτ hτs b₀ s₀ hrowf hcolf

theorem wd_prod₂_of_interleave (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x y : IrrGL k)
    (u v w : List (IrrGL k)) (_hu : ∀ c ∈ u, c.IsCusp) (_hv : ∀ c ∈ v, c.IsCusp) (hxu : Wd x.rep u)
    (hyv : Wd y.rep v) (hw : Zc.Comb.Interleave u v w) : Wd (prod₂ x.rep y.rep) w := by
  obtain ⟨X, rfl, rfl⟩ : ∃ X : Fin 2 → IrrGL k, X 0 = x ∧ X 1 = y := ⟨![x, y], rfl, rfl⟩
  exact wd_prod₂_of_interleave_fin hA X u v w hxu hyv hw

end GlobalTheory.CompanionTheory.WordProd

end
end

