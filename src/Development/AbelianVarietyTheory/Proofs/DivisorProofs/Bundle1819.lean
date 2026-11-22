import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1717
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1785
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1786
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1729
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1747
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0246
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLMulIsPrimitiveFrameDiagonalLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open ValuativeRel

namespace GlobalTheory.PrimFrameExist

theorem exists_gl_mul_isPrimFrame : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a : ℕ) (C : Type) [Fintype C] [DecidableEq C] (d : C → kˣ) (X : Matrix (Fin a) C k), X.rank = a →
    ∃ g₀ : GL (Fin a) k, IsPrimFrame (diagLat d) (g₀.val * X) := by
  intro k _ _ _ _ a C _ _ d X hX
  classical
  set Λ : Submodule 𝒪[k] (C → k) := diagLat d with hΛdef
  set V : Submodule k (C → k) := Submodule.span k (Set.range X.row) with hVdef
  set M : Submodule 𝒪[k] (C → k) := V.restrictScalars 𝒪[k] ⊓ Λ with hMdef
  have hΛfg : Λ.FG := (isLattice_diagLat d).fg
  haveI : IsNoetherian 𝒪[k] Λ := isNoetherian_of_fg_of_noetherian Λ hΛfg
  haveI : IsNoetherian 𝒪[k] M := isNoetherian_of_le inf_le_right
  haveI : Module.IsTorsionFree 𝒪[k] k := inferInstance
  haveI : Module.IsTorsionFree 𝒪[k] (C → k) := Module.IsTorsionFree.trans_faithfulSMul 𝒪[k] k (C → k)
  haveI : Module.IsTorsionFree 𝒪[k] M := inferInstance
  haveI : Module.Free 𝒪[k] M := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex 𝒪[k] M
  let b : Module.Basis ι 𝒪[k] M := Module.Free.chooseBasis 𝒪[k] M
  let v : ι → (C → k) := fun i => (b i : C → k)
  have hvV : ∀ i, v i ∈ V := fun i => (b i).2.1
  have hvΛ : ∀ i, v i ∈ Λ := fun i => (b i).2.2
  have hrepr : ∀ y (hy : y ∈ M), y = ∑ i, ((b.repr ⟨y, hy⟩ i : 𝒪[k]) : k) • v i := by
    intro y hy
    have h := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
    rw [Submodule.coe_sum] at h
    exact h.symm.trans (Finset.sum_congr rfl fun i _ => rfl)
  have hli : LinearIndependent k v := by
    rw [← LinearIndependent.iff_fractionRing (R := 𝒪[k]) (K := k)]
    exact b.linearIndependent.map' M.subtype M.ker_subtype
  have hclear : ∀ x : C → k, ∃ r : 𝒪[k], r ≠ 0 ∧ (r : k) • x ∈ Λ := by
    intro x
    obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors 𝒪[k])
      (fun j => x j / (d j : k))
    refine ⟨r, nonZeroDivisors.coe_ne_zero r, ?_⟩
    rw [hΛdef, mem_diagLat]
    intro j
    obtain ⟨s, hs⟩ := hr j
    rw [Algebra.smul_def] at hs
    have h1 : valuation k (algebraMap 𝒪[k] k r * (x j / d j)) ≤ 1 := by
      rw [← hs]; exact (Valuation.mem_integer_iff _ _).1 s.2
    have e : ((r : 𝒪[k]) : k) • x = fun l => (algebraMap 𝒪[k] k r * (x l / d l)) * d l := by
      funext l; simp only [Pi.smul_apply, smul_eq_mul]; rw [mul_assoc, div_mul_cancel₀ _ (d l).ne_zero]; rfl
    rw [e, map_mul]
    exact mul_le_of_le_one_left' h1
  have hli' : X.rank = Fintype.card (Fin a) ↔ LinearIndependent k X.row := by
    rw [rank_eq_finrank_span_row, linearIndependent_iff_card_eq_finrank_span, eq_comm]; rfl
  have hXli : LinearIndependent k X.row := hli'.1 (by simpa using hX)
  have hVle : V ≤ Submodule.span k (Set.range v) := by
    intro x hx
    obtain ⟨r, hr0, hr⟩ := hclear x
    have hrx : ((r : 𝒪[k]) : k) • x ∈ M := ⟨V.smul_mem _ hx, hr⟩
    have e := hrepr _ hrx
    have hr0' : ((r : 𝒪[k]) : k) ≠ 0 := fun h => hr0 (Subtype.ext h)
    have hx' : x = ((r : 𝒪[k]) : k)⁻¹ • (((r : 𝒪[k]) : k) • x) := (inv_smul_smul₀ hr0' x).symm
    rw [hx', e]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hspan : Submodule.span k (Set.range v) = V :=
    le_antisymm (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hvV i)) hVle
  have hcard : Fintype.card ι = a := by
    rw [← finrank_span_eq_card hli, hspan, hVdef, finrank_span_eq_card hXli, Fintype.card_fin]
  let e : Fin a ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  let Y : Matrix (Fin a) C k := Matrix.of fun i => v (e i)
  have hYV : ∀ i, Y.row i ∈ V := fun i => hvV (e i)
  choose g hg using fun i => (Submodule.mem_span_range_iff_exists_fun k).1 (hYV i)
  have hYg : (Matrix.of g) * X = Y := by
    ext i l
    have h := congrFun (hg i) l
    rw [Finset.sum_apply] at h
    rw [Matrix.mul_apply]
    exact (Finset.sum_congr rfl fun j _ => rfl).trans h
  have hYli : LinearIndependent k Y.row := hli.comp e e.injective
  have hgli : LinearIndependent k (Matrix.of g).row := by
    refine LinearIndependent.of_comp (Matrix.vecMulLinear X) ?_
    convert hYli using 1
    funext i
    rw [← hYg]
    try rfl
  have hu : IsUnit (Matrix.of g) := Matrix.linearIndependent_rows_iff_isUnit.1 hgli
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, hYg, isPrimFrame_iff]
  refine ⟨fun i => hvΛ (e i), fun c hc i => ?_⟩
  have hcV : c ᵥ* Y ∈ V := by
    rw [vecMul_eq_sum]; exact V.sum_mem fun i _ => V.smul_mem _ (hYV i)
  have hcM : c ᵥ* Y ∈ M := ⟨hcV, hc⟩
  have e1 := hrepr _ hcM
  have e2 : c ᵥ* Y = ∑ t, c (e.symm t) • v t := by
    rw [vecMul_eq_sum, ← e.sum_comp]
    exact Finset.sum_congr rfl fun i _ => by rw [e.symm_apply_apply]; rfl
  have h := Fintype.linearIndependent_iffₛ.1 hli (fun t => c (e.symm t))
    (fun t => ((b.repr ⟨_, hcM⟩ t : 𝒪[k]) : k)) (by rw [← e2, ← e1]) (e i)
  simp only [Equiv.symm_apply_apply] at h
  rw [h]
  exact (b.repr _ _).2

end GlobalTheory.PrimFrameExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFrameAndLocalFramesAllPlaces
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem top_le_preimage_of_isDominant {K : Type} [Field K] {C : Scheme.{0}} (x : Sp K ⟶ C) [IsDominant x]
    (V : C.Opens) (hV : (V : Set C).Nonempty) : ⊤ ≤ x ⁻¹ᵁ V := by
  obtain ⟨y, hy⟩ := x.denseRange.exists_mem_open V.isOpen hV
  intro z _
  have : z = y := Subsingleton.elim _ _
  subst this
  exact hy

theorem top_le_preimage_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] {C : Scheme.{0}} (b : Sp R ⟶ C)
    (V : C.Opens) (h : b (IsLocalRing.closedPoint R) ∈ V) : ⊤ ≤ b ⁻¹ᵁ V := by
  intro z _
  have hs : z ⤳ IsLocalRing.closedPoint R :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal z.2.ne_top)
  exact (hs.map b.continuous).mem_open V.isOpen h

theorem locFrame_of_frames {k K : Type} [Field k] [Field K] [Algebra k K] {C : Scheme.{0}} (x : Sp K ⟶ C)
    {W : C.Modules} {r : ℕ} {V₀ V : C.Opens} {s : Fin r → Γ(W, V₀)} {t : Fin r → Γ(W, V)}
    (hs : IsFrame s) (ht : IsFrame t) (v : Place k K) (b : Sp v.O ⟶ C) (hb : spMap v.O.subtype ≫ b = x)
    (hbV : ⊤ ≤ b ⁻¹ᵁ V) (hx : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V)) :
    LocFrame x s v (((ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))).map (evAt x hx)) ∧
      (((ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))).map (evAt x hx)).det ≠ 0 := by
  set M := (ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀)) with hM
  refine ⟨⟨b, V, t, V₀ ⊓ V, inf_le_left, inf_le_right, hx, M, hb, hbV, ht, fun j => ?_, rfl⟩, ?_⟩
  · have := (ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).sum_repr (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀) j)
    simp only [IsFrame.basis_apply] at this
    rw [hM]
    simp only [Module.Basis.toMatrix_apply, IsFrame.basis_apply]
    exact this.symm
  · have hu : IsUnit M.det := by
      have := Module.Basis.toMatrix_mul_toMatrix_flip (ht.basis (inf_le_right : V₀ ⊓ V ≤ V))
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))
      exact isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, this, Matrix.det_one]⟩
    have := (hu.map (evAt x hx)).ne_zero
    rwa [RingHom.map_det] at this

theorem unimod_one' {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v : Place k F) :
    Unimod v (1 : Matrix (Fin n) (Fin n) F) :=
  ⟨fun i j => by by_cases h : i = j <;> simp [Matrix.one_apply, h], by simp⟩

theorem exists_frame_locFrames : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∃ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty ∧ IsFrame s ∧ admitted g ∧ ∀ v, LocFrame x s v (g v) := by
  intro k K _ _ _ _ _ C _ x hx W r hW
  haveI : IsDominant x := hx.2.1.1
  have hxx : spMap (algebraMap K K) ≫ x = x := by
    change spMap (RingHom.id K) ≫ x = x
    exact (congrArg (· ≫ x) (Spec.map_id _)).trans (Category.id_comp x)
  obtain ⟨V₀, s, hη, hs⟩ := hW (x (IsLocalRing.closedPoint K))
  have hV₀ : (V₀ : Set C).Nonempty := ⟨_, hη⟩
  have hcen : ∀ v : Place k K, ∃ b : Sp v.O ⟶ C, spMap v.O.subtype ≫ b = x := fun v => by
    obtain ⟨b, hb, -⟩ := GlobalTheory.T.existsUnique_centre_functionFieldPlace_curve k K K C x hx v
    exact ⟨b, hb.trans hxx⟩
  choose b hb using hcen
  have key : ∀ v, ∃ gv : Matrix (Fin r) (Fin r) K,
      LocFrame x s v gv ∧ gv.det ≠ 0 ∧ (⊤ ≤ b v ⁻¹ᵁ V₀ → gv = 1) := by
    intro v
    by_cases hv : ⊤ ≤ b v ⁻¹ᵁ V₀
    · have hx' : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V₀) := by
        rw [inf_idem]; exact top_le_preimage_of_isDominant x V₀ hV₀
      obtain ⟨h1, h2⟩ := locFrame_of_frames x hs hs v (b v) (hb v) hv hx'
      refine ⟨_, h1, h2, fun _ => ?_⟩
      rw [Module.Basis.toMatrix_self]
      simp
    · obtain ⟨V, t, hc, ht⟩ := hW (b v (IsLocalRing.closedPoint v.O))
      have hbV := top_le_preimage_of_closedPoint (b v) V hc
      have hx' : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V) := fun z hz =>
        ⟨top_le_preimage_of_isDominant x V₀ hV₀ hz, top_le_preimage_of_isDominant x V ⟨_, hc⟩ hz⟩
      obtain ⟨h1, h2⟩ := locFrame_of_frames x hs ht v (b v) (hb v) hbV hx'
      exact ⟨_, h1, h2, fun h => absurd h hv⟩
  choose g hg1 hg2 hg3 using key
  refine ⟨V₀, s, g, hV₀, hs, ⟨hg2, ?_⟩, hg1⟩
  refine (GlobalTheory.T.finite_places_centre_outside_open k K K C x hx V₀ hV₀).subset fun v hv => ⟨b v, (hb v).trans hxx.symm, fun h => hv ?_⟩
  rw [hg3 v h]
  exact unimod_one' v

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeSequenceFirstMapLattice
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LattIota

variable {A O M : Type} [CommRing A] [CommRing O] [AddCommGroup M] [Module O M] {ι : Type}
  (θ : A →+* O) (hs : Function.Surjective θ) (R : (ι → A) →ₛₗ[θ] M)
  (hR : ∀ s : ι → A, (∀ i, θ (s i) = 0) → R s = 0)

include hR in
theorem eq_of_theta_eq {s s' : ι → A} (h : ∀ i, θ (s i) = θ (s' i)) : R s = R s' := by
  rw [← sub_eq_zero, ← map_sub]
  exact hR _ fun i => by rw [Pi.sub_apply, map_sub, h, sub_self]

def descend : (ι → O) →ₗ[O] M where
  toFun ρ := R (fun i => Function.surjInv hs (ρ i))
  map_add' ρ ρ' := by
    rw [← map_add]
    exact eq_of_theta_eq θ R hR fun i => by
      simp [Function.surjInv_eq hs]
  map_smul' c ρ := by
    have h1 : (c • R (fun i => Function.surjInv hs (ρ i)) : M) =
        θ (Function.surjInv hs c) • R (fun i => Function.surjInv hs (ρ i)) := by
      rw [Function.surjInv_eq hs]
    rw [RingHom.id_apply, h1, ← LinearMap.map_smulₛₗ]
    exact eq_of_theta_eq θ R hR fun i => by
      simp [Function.surjInv_eq hs]

theorem descend_comp (s : ι → A) : descend θ hs R hR (fun i => θ (s i)) = R s :=
  eq_of_theta_eq θ R hR fun i => Function.surjInv_eq hs _

variable [Fintype ι]

def dotL (ρ : ι → O) : (ι → O) →ₗ[O] O where
  toFun w := ρ ⬝ᵥ w
  map_add' := dotProduct_add ρ
  map_smul' c w := by rw [dotProduct_smul, RingHom.id_apply]

@[simp] theorem dotL_apply (ρ w : ι → O) : dotL ρ w = ρ ⬝ᵥ w := rfl

end GlobalTheory.LattIota

namespace GlobalTheory.LattIota

theorem iota_exists : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G : PDivGroup p O), HasDatum hε G → ∀ (M : Type) [AddCommGroup M] [Module O M] (r : latt G →ₛₗ[WittVector.fontaineTheta O p] M) (π : M →ₗ[O] G.dual.Lie), Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = xi ε • n) → (∀ (y : latt G) t, π (r y) (hodgeTate G t) = WittVector.fontaineTheta O p (y.1 t)) → ∃ ι : G.omega →ₗ[O] M, Function.Injective ι ∧ Function.Exact ι π ∧ (∀ (χ : G.dual.Tate) (y : latt G), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) → ι (dlog G χ) = r y) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG M _ _ r π hrs hker hπ
  obtain ⟨D, e, fil, lie, hal, hb⟩ := hG
  obtain ⟨L, hL⟩ := GlobalTheory.T.hodgeTate_lattice_eq_rowSpace_of_sandwich_datum p C v O hv ε hε G G.height D e fil hal
  have hε1 : IsPrimitiveRoot (root ε).untilt p := by
    simpa [zeta] using hε 1
  obtain ⟨hdom, -, hkerθ, hsθ, hν, hξ, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε1
  obtain ⟨hFG, hrangeFil, -, hνFil, -, -⟩ :=
    GlobalTheory.Sandwich.HodgeTateBound.bound p C v O hv ε hε1 ℤ_[p] G.height D
  obtain ⟨hFin, hProj⟩ := GlobalTheory.PDiv.omega_finite_projective p C v O hv G
  have hθξ : WittVector.fontaineTheta O p (xi ε) = 0 := by
    rw [← RingHom.mem_ker, hkerθ]; exact Ideal.mem_span_singleton_self _
  let R : (Fin G.height → Ainf p O) →ₛₗ[WittVector.fontaineTheta O p] M :=
    r.comp (L : (Fin G.height → Ainf p O) →ₗ[Ainf p O] latt G)
  have hR : ∀ s : Fin G.height → Ainf p O, (∀ i, WittVector.fontaineTheta O p (s i) = 0) →
      R s = 0 := by
    intro s hs0
    have hu : ∀ i, ∃ u, u * xi ε = s i := fun i => by
      rw [← Ideal.mem_span_singleton', ← hkerθ]; exact hs0 i
    choose u hu using hu
    have hsu : s = xi ε • u := funext fun i => by rw [Pi.smul_apply, smul_eq_mul, mul_comm, hu]
    change r (L s) = 0
    rw [hker, hsu, map_smul]
    exact ⟨_, rfl⟩
  let Φ := descend _ hsθ R hR
  have hΦ : ∀ s, Φ (fun i => WittVector.fontaineTheta O p (s i)) = r (L s) := fun s =>
    descend_comp _ hsθ R hR s
  have hlift : ∀ ρ : Fin G.height → O, ∃ s : Fin G.height → Ainf p O,
      (fun i => WittVector.fontaineTheta O p (s i)) = ρ := fun ρ =>
    ⟨fun i => Function.surjInv hsθ (ρ i), funext fun i => Function.surjInv_eq hsθ _⟩
  have hΦs : Function.Surjective Φ := by
    intro m
    obtain ⟨y, rfl⟩ := hrs m
    obtain ⟨s, rfl⟩ := L.surjective y
    exact ⟨_, hΦ s⟩
  have hΦi : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ρ hρ
    obtain ⟨s, rfl⟩ := hlift ρ
    rw [hΦ, hker] at hρ
    obtain ⟨n, hn⟩ := hρ
    have hs : s = xi ε • L.symm n := by
      apply L.injective; rw [map_smul, L.apply_symm_apply, hn]
    funext i
    rw [hs, Pi.smul_apply, smul_eq_mul, map_mul, hθξ, zero_mul, Pi.zero_apply]
  have hπHT : ∀ s t, π (r (L s)) (hodgeTate G t) =
      (fun i => WittVector.fontaineTheta O p (s i)) ⬝ᵥ (fil (hodgeTate G t) : Fin G.height → O) := by
    intro s t
    rw [hπ, hL, ← hal, RingHom.map_dotProduct]
    congr 1
    funext i
    rw [Function.comp_apply, RingHom.map_mulVec]
    rfl
  have hsingle : ∀ i, toO e (e.symm (Pi.single i 1)) = Pi.single i 1 := by
    intro i; funext j
    by_cases hij : j = i
    · subst hij; simp [toO]
    · simp [toO, Pi.single_apply, hij]
  have hext : ∀ f₁ f₂ : G.dual.omega →ₗ[O] O,
      (∀ t, f₁ (hodgeTate G t) = f₂ (hodgeTate G t)) → f₁ = f₂ := by
    intro f₁ f₂ hf
    let g : (G.dual.omega →ₗ[O] O) → (Fin G.height → O) →ₗ[O] O := fun f =>
      f ∘ₗ fil.symm.toLinearMap ∘ₗ (D.al.codRestrict D.Fil (fun w => hrangeFil ⟨w, rfl⟩))
    have key : ∀ f t, g f (toO e t) = f (hodgeTate G t) := by
      intro f t
      have h1 : D.al.codRestrict D.Fil (fun w => hrangeFil ⟨w, rfl⟩) (toO e t) =
          fil (hodgeTate G t) := Subtype.ext (hal t)
      simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, LinearEquiv.symm_apply_apply]
    have hg : g f₁ = g f₂ := by
      refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
      change g f₁ (Pi.single i 1) = g f₂ (Pi.single i 1)
      rw [← hsingle, key, key, hf]
    refine LinearMap.ext fun x => ?_
    obtain ⟨w, hw⟩ := hνFil _ (fil x).2
    have hgx : ∀ f, g f w = WittVector.fontaineTheta O p (nu ε) * f x := by
      intro f
      have h1 : D.al.codRestrict D.Fil (fun w => hrangeFil ⟨w, rfl⟩) w =
          WittVector.fontaineTheta O p (nu ε) • fil x := Subtype.ext hw
      simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, map_smul,
        LinearEquiv.symm_apply_apply, smul_eq_mul]
    exact mul_left_cancel₀ hν (by rw [← hgx, ← hgx, hg])
  have hπΦ : ∀ ρ x, π (Φ ρ) x = ρ ⬝ᵥ (fil x : Fin G.height → O) := by
    intro ρ
    obtain ⟨s, rfl⟩ := hlift ρ
    have := hext (π (Φ (fun i => WittVector.fontaineTheta O p (s i))))
      (dotL (fun i => WittVector.fontaineTheta O p (s i)) ∘ₗ D.Fil.subtype ∘ₗ fil.toLinearMap)
      (fun t => by rw [hΦ, hπHT]; rfl)
    intro x
    exact LinearMap.congr_fun this x
  let κ : G.omega →ₗ[O] (Fin G.height → O) :=
    LinearMap.pi fun i => lie (D.Fil.mkQ (Pi.single i 1))
  have hκ : ∀ w i, κ w i = lie (D.Fil.mkQ (Pi.single i 1)) w := fun w i => rfl
  have hk : ∀ w m, κ w ⬝ᵥ m = lie (D.Fil.mkQ m) w := by
    intro w
    have : dotL (κ w) = (LinearMap.applyₗ w : Module.Dual O G.omega →ₗ[O] O) ∘ₗ
        lie.toLinearMap ∘ₗ D.Fil.mkQ := by
      refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
      simp [hκ]
    intro m
    exact LinearMap.congr_fun this m
  have hκi : Function.Injective κ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine (Module.forall_dual_apply_eq_zero_iff O w).1 fun φ => ?_
    obtain ⟨q, rfl⟩ := lie.surjective φ
    obtain ⟨m, rfl⟩ := D.Fil.mkQ_surjective q
    rw [← hk, hw, zero_dotProduct]
  refine ⟨Φ ∘ₗ κ, hΦi.comp hκi, fun m => ⟨fun h0 => ?_, ?_⟩, ?_⟩
  · obtain ⟨ρ, rfl⟩ := hΦs m
    have hρ : D.Fil ≤ LinearMap.ker (dotL ρ) := fun f hf => by
      obtain ⟨x, hx⟩ := fil.surjective ⟨f, hf⟩
      have := LinearMap.congr_fun h0 x
      rw [hπΦ, hx] at this
      exact this
    let ψ : ((Fin G.height → O) ⧸ D.Fil) →ₗ[O] O := D.Fil.liftQ (dotL ρ) hρ
    let w := (Module.evalEquiv O G.omega).symm (ψ ∘ₗ lie.symm.toLinearMap)
    have hw : ∀ φ : G.Lie, φ w = ψ (lie.symm φ) := fun φ => by
      change (Module.evalEquiv O G.omega w) φ = _
      rw [LinearEquiv.apply_symm_apply]
      rfl
    refine ⟨w, ?_⟩
    change Φ (κ w) = Φ ρ
    congr 1
    funext i
    rw [hκ, hw, LinearEquiv.symm_apply_apply]
    simp [ψ]
  · rintro ⟨w, rfl⟩
    refine LinearMap.ext fun x => ?_
    change π (Φ (κ w)) x = 0
    rw [hπΦ, hk, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 (fil x).2, map_zero]
    rfl
  · intro χ y hy
    let sχ : Fin G.height → Ainf p O := fun i =>
      ofPadic p O (epsPairing hε G (e.symm (Pi.single i 1)) χ)
    have hpair : ∀ t, sχ ⬝ᵥ (fun i => ofPadic p O (e t i)) = ofPadic p O (epsPairing hε G t χ) := by
      intro t
      have ht : t = ∑ i, e t i • e.symm (Pi.single i 1) := by
        apply e.injective
        rw [map_sum]
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      have hlin : epsPairing hε G t χ =
          ∑ i, e t i * epsPairing hε G (e.symm (Pi.single i 1)) χ := by
        conv_lhs => rw [ht]
        simp only [epsPairing, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
          smul_eq_mul]
      rw [hlin, map_sum]
      simp only [dotProduct, sχ, map_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hyL : y = L (sχ ᵥ* D.G) := by
      apply Subtype.ext
      refine LinearMap.ext fun t => ?_
      rw [hL, hy, ← dotProduct_mulVec, mulVec_mulVec, D.G_mul_F, smul_mulVec, one_mulVec,
        dotProduct_smul, hpair, smul_eq_mul]
    rw [hyL, ← hΦ]
    change Φ (κ (dlog G χ)) = _
    congr 1
    funext i
    rw [hκ, ← hb, LinearEquiv.symm_apply_apply, RingHom.map_vecMul]
    simp [bQuot, pairingO, Datum.bb, Matrix.toLin'_apply, vecMul, dotProduct, padicToO, sχ,
      mul_comm]

end GlobalTheory.LattIota
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPlaneSplitHermitianLatticeSpaceStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hyperbolicPlane_split_hermitianLatticeSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ), n = n₁ + 2 → 1 ≤ n₁ → ∀ (Y : Spc F E n) (r s : ℕ), 1 ≤ r → 1 ≤ s →
    Y.IsHerm σ B r s → ∀ i₀ i₁ : ℕ, i₀ < i₁ → i₁ < n → ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
      (GlobalTheory.ThK.reS Y Y').IsHerm σ B r s ∧ Y₁.IsHerm σ B (r - 1) (s - 1) ∧ H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁ := by
  first | exact @GlobalTheory.KTowerPlane.exists_hyperbolic_split | exact GlobalTheory.KTowerPlane.exists_hyperbolic_split | (intros; apply GlobalTheory.KTowerPlane.exists_hyperbolic_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLimitPowersIntegralAdelesStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_limit_powers_integralAdeles : ∀ (D : D7) (x : 𝓞 D.host.E), ∃ e ∈ OhE D, e * e = e ∧ ∀ N : ℕ, 0 < N → ∃ n : ℕ, 0 < n ∧ ∃ w ∈ OhE D, e = inc D (x : D.host.E) ^ n + (N : AE D) * w := by
  first | exact @GlobalTheory.AlgIntIdem.idem | exact GlobalTheory.AlgIntIdem.idem | (intros; apply GlobalTheory.AlgIntIdem.idem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentPowerLimitCongruentOneStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_powerLimit_congruentOne : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ y ∈ OhE D, y - 1 ∈ hatId D 𝔪 → ∃ g ∈ OhE D, y * g * (y * g) = y * g ∧ y * g - 1 ∈ hatId D 𝔪 := by
  first | exact @GlobalTheory.PowIdem.exists_idem | exact GlobalTheory.PowIdem.exists_idem | (intros; apply GlobalTheory.PowIdem.exists_idem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitaryGlueIdempotentStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralUnitary_glue_idempotent : ∀ (D : D7) (𝔫 : Ideal (𝓞 D.host.E)) (a : ℕ) (Z : Matrix (Fin a) (Fin a) (𝓞 D.host.E)) (f w : AE D), f ∈ OhE D → w ∈ OhE D → f * f = f → f * sgA D f = 0 → f = inc D ((Z.det : 𝓞 D.host.E) : D.host.E) * w → 1 - f ∈ hatId D 𝔫 → ∃ k ∈ intG D a, ∀ i l, (Z.map (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) - (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l ∈ hatId D 𝔫 := by
  first | exact @GlobalTheory.GlueUnitary.glue_unitary | exact GlobalTheory.GlueUnitary.glue_unitary | (intros; apply GlobalTheory.GlueUnitary.glue_unitary <;> assumption)
end

